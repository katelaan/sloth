"""Custom representation of a parsed SL expression tree.

We have our own representation for easier manipulation and
bookkeeping.

.. testsetup::

   from sloth import *
   from sloth.encoder import exponential as e
   from sloth.encoder import preproc
   from sloth.encoder.astbuilder import processed_ast
   from sloth.encoder.slast import *

"""

from z3 import is_const, And, Or, Not, ExprRef

from ..backend import symbols
from ..utils import utils
from ..z3api import z3utils
from .utils import EncoderState
from . import astutils

class SlAst:

    def __init__(self):
        self.state = EncoderState.Initial

    def is_leaf(self):
        return True

    def is_pred_call(self):
        return False

    def is_data(self):
        return False

    def __iter__(self):
        # It is possible to iterate over the children of SlAst objects
        # By default, an Sl syntax element is assumed to be at the leaf
        # We thus return an empty iterator here
        return iter(())

    def is_positive(self):
        # By default, a formula is positive if all its children are
        # This is overridden in the negation, where it's of course the opposite
        return all(child.is_positive() for child in self)

    # Outside assign_ids to ensure unique ids throughout the lifetime of the code -- in particular, when additional ASTs are built from within PredCalls
    id_ = [0]
    # TODO: Does this solve issues with stop nodes? E.g.: ls(x,y) * ls(y) /\ not ls(x)? And more complicated examples of this kind?
    _id_dict = {}

    def _state_transition(self, src, trg):
        assert(self.state >= src)
        self.state = trg

def _rep(obj, args):
    reps = [repr(arg) for arg in args]
    return "{}({})".format(type(obj).__name__, ", ".join(reps))

class PointsTo(SlAst):
    """Representation of sl.struct.pointsto(src, trg_0,...trg_k).

    >>> t = processed_ast(sl.structs, sl.tree.pointsto("a", "b", "c"))
    >>> e.encode_ast(t, {}) # doctest: +NORMALIZE_WHITESPACE
    Encoding[...]

    """

    def __init__(self, struct, src, *trg):
        super().__init__()
        self.struct = struct
        self.src = src
        self.trg = list(trg)

    def to_sl_expr(self):
        return self.struct.points_to_predicate()(self.src, *self.trg)

    def loc_consts(self):
        yield self.src
        for fld, trg in zip(self.struct.points_to_fields, self.trg):
            if not self.struct.is_data_field(fld):
                yield trg

    def data_consts(self):
        for fld, trg in zip(self.struct.points_to_fields, self.trg):
            if self.struct.is_data_field(fld):
                yield trg

    def __repr__(self):
        args = [self.struct.name, self.src] + self.trg
        return _rep(self, args)

class PointsToSingleField(SlAst):
    """Representation of sl.struct.fld(src, trg).

    >>> t = processed_ast(sl.structs, sl.list.next("a", "b"))
    >>> e.encode_ast(t, {}) # doctest: +NORMALIZE_WHITESPACE
    Encoding[...]
    >>> t = processed_ast(sl.structs, sl.list.data("a", "b"))
    >>> e.encode_ast(t, {}) # doctest: +NORMALIZE_WHITESPACE
    Encoding[...]

    """

    def __init__(self, struct, fld, src, trg):
        super().__init__()
        self.struct = struct
        self.src = src
        self.fld = fld
        self.trg = trg

    def to_sl_expr(self):
        return self.struct.fld_predicate(self.fld)(self.src, self.trg)

    def loc_consts(self):
        yield self.src
        if not self.struct.is_data_field(self.fld):
            yield self.trg

    def data_consts(self):
        if self.struct.is_data_field(self.fld):
            yield self.trg

    def __repr__(self):
        args = [self.struct.name, self.fld, self.src, self.trg]
        return _rep(self, args)

class PredCall(SlAst):
    """A spatial predicate call (i.e., without data parameter).

    >>> p = PredCall(sl.list.struct, None, None, sl.list.loc("a"))
    >>> p.is_leaf()
    True
    >>> p.is_pred_call()
    True

    """

    def __init__(self, struct, fld, pred, root, *stop_nodes):
        super().__init__()
        # Both None => Core, spatial predicate call
        assert (fld is None) or isinstance(fld, str)
        assert (fld is None) or (pred is not None), \
                'Data predicate field is set, but not the predicate itself'
        assert isinstance(root, ExprRef), \
            'Cannot use {} of type {} as data structure root'.format(root, type(root).__name__)
        self.struct = struct
        self.fld = fld
        self.pred = pred
        self.root = root
        self.stop_nodes = list(stop_nodes)

    def to_sl_expr(self):
        if self.pred is None:
            # Spatial predicate call
            if not self.stop_nodes:
                return self.struct.predicate()(self.root)
            else:
                fun = self.struct.segment_predicate(len(self.stop_nodes))
                return fun(self.root, *self.stop_nodes)
        else:
            # Data predicate call
            fun = self.struct.data_predicate(self.fld, len(self.stop_nodes))
            return fun(self.pred.to_sl_expr(), self.root, *self.stop_nodes)

    def is_pred_call(self):
        return True

    def loc_consts(self):
        yield self.root
        for n in self.stop_nodes:
            yield n

    @staticmethod
    def _is_template_var(x):
        sx = str(x)
        return sx == 'sl.alpha' or sx == 'sl.beta'

    def data_consts(self):
        if self.pred is not None:
            for data_atom in astutils.atoms(self.pred):
                assert isinstance(data_atom, DataAtom), utils.wrong_type(data_atom)
                for d in z3utils.collect_consts(data_atom.atom):
                    #print('Considering yielding {}'.format(d))
                    if not PredCall._is_template_var(d):
                        #print('Will yield const {}'.format(d))
                        yield d

    def __repr__(self):
        args = [self.struct.name, self.fld, self.pred, self.root] + self.stop_nodes
        return _rep(self, args)

class SpatialEq(SlAst):
    def __init__(self, struct, negated, left, right):
        super().__init__()
        self.struct = struct
        self.negated = negated
        self.left = left
        self.right = right

    def to_sl_expr(self):
        if self.negated:
            return self.struct.disequality_predicate()(self.left, self.right)
        else:
            return self.struct.equality_predicate()(self.left, self.right)

    def __repr__(self):
        args = [self.left, self.right, self.negated]
        return _rep(self, args)

    def loc_consts(self):
        yield self.left
        yield self.right

    def data_consts(self):
        if False:
            yield

class DataAtom(SlAst):
    """Representation of atomic formulas in the data part.

    >>> a = Int("a")
    >>> t = processed_ast(sl.structs, a < 42)
    >>> e.encode_ast(t, {}) # doctest: +NORMALIZE_WHITESPACE
    Encoding[...]

    """

    def __init__(self, atom):
        super().__init__()
        self.atom = atom
        self.fps = {} # Data atoms have no spatial content!

    def is_data(self):
        return True

    def to_sl_expr(self):
        return self.atom

    def __repr__(self):
        return _rep(self, [self.atom])

    def loc_consts(self):
        if False:
            yield

    def data_consts(self):
        for arg in self.atom.children():
            if not symbols.data_literal_check(arg):
                # Make sure not to add literals
                yield arg

class Op(SlAst):

    def __repr__(self):
        return _rep(self, iter(self))

    def is_leaf(self):
        return False

    def __getitem__(self, i):
        it = iter(self)
        j = -1
        while j < i:
            res = next(it)
            j += 1
        return res

    def to_sl_expr(self):
        sub_exprs = (child.to_sl_expr() for child in self)
        return self.smt_decl(*sub_exprs)

class BinOp(Op):
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right

    def __iter__(self):
        yield self.left
        yield self.right

class SepCon(BinOp):
    """A binary separating conjunction.

    >>> expr = sl.sepcon(sl.list.pointsto("a", "b"), sl.list.pointsto("b", "c"))
    >>> t = processed_ast(sl.structs, expr)
    >>> e.encode_ast(t, {}) # doctest: +NORMALIZE_WHITESPACE
    Encoding[...]

    """

    smt_decl = symbols.sep_con_fn
    fp_letter = "S"

    def __init__(self, left, right):
        super().__init__(left, right)

class SlAnd(BinOp):

    smt_decl = symbols.and_decl
    fp_letter = 'A'

    def __init__(self, left, right):
        super().__init__(left, right)

class SlOr(BinOp):

    smt_decl = symbols.or_decl
    fp_letter = 'O'

    def __init__(self, left, right):
        super().__init__(left, right)

class SlNot(Op):

    smt_decl = symbols.not_decl
    fp_letter = 'N'

    def __init__(self, arg):
        super().__init__()
        self.arg = arg

    def __iter__(self):
        yield self.arg

    def is_positive(self):
        return not self.arg.is_positive()
