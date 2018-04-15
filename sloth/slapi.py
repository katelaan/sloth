"""
Provides a programmatic API for creating separation logic expressions.

See the documentation of :class:`sloth.slapi.SlApi` for details.

.. testsetup::

      import z3
      from sloth.slapi import *
      from sloth.backend import LambdaBackend
      from sloth import api

"""

import functools

import z3

from . import consts, config
from .utils import utils
from .backend import symbols, generic, struct

def _constify(struct, term):
    if isinstance(term, str):
        return struct.sort[term]
    else:
        assert z3.is_const(term), '{} : {} is no constant'.format(term, type(term).__name__)
        return term

def _fp_constify(struct, term):
    if isinstance(term, str):
        return struct.fp_sort[term]
    else:
        assert isinstance(term, generic.Set), utils.wrong_type(term)
        return term

class SlApi:
    """Programmatic API for creating separation logic expressions.

    Mimics the identifiers available in our SMTLIB-style format, but
    builds :class:`z3.ExprRef` instances directly rather than going
    through z3's parser.

    >>> sl = SlApi(LambdaBackend)
    >>> sl.list.null
    sl.list.null
    >>> sl.list.pointsto('a', 'b')
    sl.list.pointsto(a, b)
    >>> api.is_sat(sl.list.pointsto('a', 'b'))
    True
    >>> sl.list.pointsto('a', sl.list.null)
    sl.list.pointsto(a, sl.list.null)
    >>> expr = sl.sepcon(sl.list.pointsto('a', 'b'), sl.list.pointsto('a', 'c'))
    >>> expr
    sl.sepcon(sl.list.pointsto(a, b), sl.list.pointsto(a, c))
    >>> api.is_sat(expr, override_bound = 2)
    False
    >>> z3.And(sl.tree('a'), sl.list('b'))
    And(sl.tree(a), sl.list(b))
    >>> sl.sepcon(sl.tree.seg('a', 'b'),sl.tree.seg2('a', 'b', 'c'))
    sl.sepcon(sl.tree.seg(a, b), sl.tree.seg2(a, b, c))
    >>> sl.sepcon(sl.tree('a'), sl.tree('b'), sl.tree('c'))
    sl.sepcon(sl.tree(a), sl.sepcon(sl.tree(b), sl.tree(c)))
    >>> sl.submodel(sl.list.seg('a','b'))
    sl.submodel(sl.list.seg(a, b))

    We can also get the special data predicate variables to build data preds:

    >>> sl.alpha
    sl.alpha
    >>> sl.list.dpred.next(sl.alpha < sl.beta, 'x')
    sl.list.dpred.next(sl.alpha < sl.beta, x)
    >>> sl.tree.dpred.right1(sl.alpha > sl.beta, 'r', 'z')
    sl.tree.dpred.right1(sl.alpha > sl.beta, r, z)

    All these calls build standard :class:`z3.ExprRef` instances, so
    they can be freely combined with calls to the z3 API. For example:

    >>> a, b = sl.list.locs('a b')
    >>> z3.And(z3.Not(b == sl.list.null), sl.list.pointsto(a,b))
    And(Not(b == sl.list.null), sl.list.pointsto(a, b))

    """

    def __init__(self, backend):
        """Construct API in which exactly the given structures are defined.

        Uses the unqualified names of the structures to choose the
        attribute names.

        """
        self.structs = struct.make_predef_structs(backend)
        for s in self.structs:
            setattr(self, s.unqualified_name, StructApi(s))

        #for i in range(config.MAX_BRANCHING+1):
        #    setattr(self, consts.DATA_VAR + str(i), symbols.data_pred_var(i))
        self.alpha = symbols.data_pred_var(0)
        self.beta = symbols.data_pred_var(1)

    @staticmethod
    def submodel(child):
        "Wrap a submodel assertion around the child."
        assert isinstance(child, z3.ExprRef), utils.wrong_type(child)
        return symbols.submodel_fn(child)

    @staticmethod
    def sepcon(l, r, *args):
        "Build n-ary separating conjunction for n >= 2 arguments."
        assert isinstance(l, z3.ExprRef), utils.wrong_type(l)
        assert isinstance(r, z3.ExprRef), utils.wrong_type(r)
        for arg in args:
            assert isinstance(arg, z3.ExprRef), utils.wrong_type(arg)
        if len(args) > 0:
            r = SlApi.sepcon(r, *args)
        return symbols.sep_con_fn(l, r)

class StructApi:
    """API for constructing assertions for an underlying recursive structure.

    The structure is passed to the constructor. For example usage, see
    :class:`SlApi`.

    """

    def __init__(self, struct):
        self.struct = struct
        self.null = struct.null
        # Single-field allocations
        for f in struct.fields:
            setattr(self, f, functools.partial(self._fld_predicate, f))
        # Segment predicates
        for i in range(config.max_num_stops(struct)):
            suffix = str(i+1) if i > 0 else ''
            setattr(self, consts.SEG_SUFFIX[1:] + suffix,
                    functools.partial(self._segment_predicate, i+1))
        # Data predicates
        setattr(self, consts.DATA_PRED_SUFFIX[1:], DataApi(struct))

    def __call__(self, *args):
        """Build a predicate call for the underlying structure.

        :param: args: Parameters for the predicate call (strings or consts)

        :rtype: :class:`z3.ExprRef`"""
        return self.struct.predicate()(*self._const(args))

    def loc(self, arg):
        """Returns a location constant for the given argument.

        >>> sl = SlApi(LambdaBackend)
        >>> a = sl.list.loc('a')
        >>> a
        a
        >>> z3.is_const(a)
        True

        """
        return _constify(self.struct, arg)

    def locs(self, *args):
        """Returns a tuple of location constants for the given arguments.

        Can be invoked both with a single space-separated string and
        with one parameter per location.

        >>> sl = SlApi(LambdaBackend)
        >>> sl.list.locs('a', 'b', 'c')
        [a, b, c]
        >>> sl.list.locs('a b c')
        [a, b, c]

        """
        args = utils.splitarg_or_varargs(*args)
        return [_constify(self.struct, arg) for arg in args]

    def fp(self, arg):
        """Returns a footprint set for the given argument.

        >>> sl = SlApi(LambdaBackend)
        >>> sl.tree.fp('X')
        X : SET(Int)

        """
        return _fp_constify(self.struct, arg)

    def fps(self, *args):
        """Returns a tuple of footprint sets for the given arguments.

        >>> sl = SlApi(LambdaBackend)
        >>> sl.tree.fps('X', 'Y')
        (X : SET(Int), Y : SET(Int))

        """
        return tuple(_fp_constify(self.struct, arg) for arg in args)

    def pointsto(self, *args):
        """The points-to predicate for the underlying structure."""
        return self.struct.points_to_predicate()(*self._const(args))

    def eq(self, x, y):
        """An equality in the spatial part"""
        return self.struct.equality_predicate()(*self._const([x, y]))

    def neq(self, x, y):
        """An equality in the spatial part"""
        return self.struct.disequality_predicate()(*self._const([x, y]))

    def _fld_predicate(self, f, src, trg):
        return self.struct.fld_predicate(f)(*self._const([src, trg]))

    def _segment_predicate(self, n, *args):
        return self.struct.segment_predicate(n)(*self._const(args))

    def _const(self, args):
        return [_constify(self.struct, arg) for arg in args]

class DataApi:
    """Api for constructing data predicates.

    For example usage, see :class:`SlApi`.

    """
    def __init__(self, struct):
        self.struct = struct
        for f in struct.fields:
            for i in range(config.max_num_stops(struct) + 1):
                suffix = str(i) if i > 0 else ''
                setattr(self, f + suffix, functools.partial(self._data_predicate, f, i))
        for i in range(config.max_num_stops(struct) + 1):
                suffix = str(i) if i > 0 else ''
                setattr(self, consts.UNARY_DP_SUFFIX + suffix, functools.partial(self._unary_data_predicate, i))

    def _unary_data_predicate(self, n, *args):
        return self.struct.unary_data_predicate(n)(args[0], *self._const(args[1:]))

    def _data_predicate(self, f, n, *args):
        return self.struct.data_predicate(f, n)(args[0], *self._const(args[1:]))

    # TODO: Remove code duplication wrt StructApi
    def _const(self, args):
        return [_constify(self.struct, arg) for arg in args]
