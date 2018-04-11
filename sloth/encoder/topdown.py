"""Encoding of non-call SL formulas.

.. testsetup::

   import functools
   import z3
   from sloth import *
   from sloth.encoder.topdown import *
   from sloth.model.checks import evaluate_to_graph

We test the encoder for formulas that do not contain calls. Formulas
with calls are tested separately for each call encoding.

Note that for some inputs that don't explicitly reference null,
whether z3 includes null in the model cannot be predicted. In such
cases, we pass the `ignore_null` flag to the evaluation function to
suppress including null nodes in the graph model. This way we don't
care whether null is in z3's model or not.

Single pointers and small separating conjunctions of pointers / equalities
--------------------------------------------------------------------------

>>> is_sat = functools.partial(sl_expr_is_sat, sl)
>>> eval_ = functools.partial(evaluate_to_graph, sl)
>>> x, y, z = sl.list.locs('x y z'); t, u, v, w = sl.tree.locs('t u v w'); d, e, f = z3.Ints('d e f')
>>> is_sat(sl.list.pointsto(x, y))
True
>>> eval_(sl.list.pointsto(x, y))
Graph({0, 1, 2}, {(1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2})
>>> eval_(sl.tree.pointsto(t, u, v))
Graph({0, 1, 2, 3}, {(1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3})
>>> eval_(sl.tree.left(t,u))
Graph({0, 1, 2}, {(1, 'left'): 2}, {'sl.tree.null': 0, 't': 1, 'u': 2})
>>> eval_(sl.sepcon(sl.tree.left(t,u), sl.tree.right(t,v)))
Graph({0, 1, 2, 3}, {(1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3})
>>> eval_(sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z)))
Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})
>>> eval_(sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null)))
Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})
>>> eval_(sl.list.eq(x,y))
Graph({0}, {}, {'x': 0, 'y': 0})
>>> eval_(sl.sepcon(sl.list.pointsto(x, y), sl.list.eq(x, y)))
Graph({0, 1}, {(1, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 1})

Mixing data structures in one expression:

>>> eval_(sl.sepcon(sl.list.pointsto(x,y), sl.tree.pointsto(t,u,v)), ignore_null = True)
Graph({0, 1, 2, 3, 4}, {(0, 'left'): 1, (0, 'right'): 2, (3, 'next'): 4}, {'t': 0, 'u': 1, 'v': 2, 'x': 3, 'y': 4})

Input with Boolean structure
----------------------------

>>> eval_(z3.And(sl.list.pointsto(x,y), sl.list.pointsto(z, y)))
Graph({0, 1, 2}, {(1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 1})
>>> eval_(z3.And(sl.list.pointsto(x,y), sl.list.pointsto(x, sl.list.null)))
Graph({0, 1}, {(1, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 0})
>>> eval_(z3.Or(sl.list.pointsto(x,y), sl.tree.pointsto(t, u, v)), ignore_null = True)
Graph({0, 1, 2, 3}, {(0, 'left'): 1, (0, 'right'): 2}, {'t': 0, 'u': 1, 'v': 2, 'x': 3})
>>> eval_(z3.Not(sl.list.pointsto(x,y)))
Graph({0}, {}, {'x': 0})
>>> eval_(z3.And(sl.list.pointsto(y,x), z3.Not(sl.list.pointsto(x,y))))
Graph({0, 1, 2}, {(2, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 2})
>>> eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, z)), sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, x))))
Graph({0, 1, 2}, {(1, 'next'): 2, (2, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 1})
>>> eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, z)), z3.Not(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, x)))))
Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})

Simple unsatisfiable benchmarks
-------------------------------

>>> is_sat(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(x,y)))
False
>>> is_sat(z3.And(sl.list.pointsto(x, y), z3.Not(sl.list.pointsto(x,y))))
False
>>> is_sat(z3.And(sl.sepcon(sl.list.pointsto(x, y), sl.list.eq(x, z)), z3.Not(sl.list.pointsto(z, y))))
False

Benchmarks with data constraints
--------------------------------

In the following test cases, there is sometimes more than one choice
for satisfying the data constraints. The current version of z3 gives a
deterministic output for these, so checking for graph isomorphism is
still fine. But with other versions of z3, some test cases might
actually break even though the code is correct. (Larger values than 43
and 9000 for the third and fourth benchmark below.)

>>> eval_(sl.sepcon(sl.list.data(x,d), d == 42))
Graph({0, 1}, {(1, 'data'): 42}, {'sl.list.null': 0, 'x': 1}, {'d': 42})
>>> eval_(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d == 42))
Graph({0, 1, 2}, {(1, 'data'): 42, (1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 42})
>>> eval_(z3.And(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d > 42), sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d < 9000)))
Graph({0, 1, 2}, {(1, 'data'): 43, (1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 43})
>>> eval_(z3.And(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d > 42), z3.Not(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d < 9000))))
Graph({0, 1, 2}, {(1, 'data'): 9000, (1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 9000})

"""

import functools, itertools

from z3 import And, Not, Or

from .. import consts as consts_mod
from ..utils import utils, logger
from ..z3api import z3utils
from . import constraints as c
from . import slast
from . import astbuilder
from . import astutils
from . import direct
from .shared import *

def structs_in_expr(sl, sl_expr):
    """
    >>> structs_in_expr(sl, sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null)))
    [Struct(sl.list)]
    >>> structs_in_expr(sl, z3.And(sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null)), z3.Not(sl.sepcon(sl.tree.left(t,u),sl.tree.right(t,v)))))
    [Struct(sl.list), Struct(sl.tree)]

    """

    d = { tuple(s.parsable_decls()) : s for s in sl.structs}

    def local_structs(sl_expr):
        return { s for fns, s in d.items() if sl_expr.decl() in fns }

    def leaf(sl_expr):
        return local_structs(sl_expr)

    def inner(sl_expr, folding):
        return set(itertools.chain(local_structs(sl_expr), *folding))

    return list(sorted(z3utils.expr_fold(sl_expr, leaf, inner), key=str))


# TODO: Have a separate API module for the encoder package

def model_of_sl_expr(sl, sl_expr):
    from .. import z3api
    e = encode_sl_expr(sl, sl_expr)
    if z3api.is_sat(e.to_z3_expr()):
        return e.label_model(z3api.model())
    else:
        return None

def sl_expr_is_sat(sl, sl_expr):
    from .. import z3api
    e = encode_sl_expr(sl, sl_expr)
    return z3api.is_sat(e.to_z3_expr())

def encode_sl_expr(sl, sl_expr, override_bound = None):
    structs = structs_in_expr(sl, sl_expr)
    ast = astbuilder.ast(structs, sl_expr)
    bounds = compute_size_bounds(structs, ast)
    if override_bound is not None:
        bounds = {s : override_bound for s in bounds}
    # TODO: Can we have one set of fresh variables and one delta formula per struct? Meaning that we can encode lists and trees separately?
    n = sum(bounds.values())
    if n > 0:
        if override_bound is not None:
            note = ' [MANUAL OVERRIDE]'
        else:
            note = ''
        print('Computed bounds: {}{}'.format(bounds, note))
        # TODO: Get rid of the explicit sort in the direct encoder API
        global_encoder_fn = functools.partial(direct.is_bounded_heap_interpretation, n, structs)
        # TODO: Ensure we pass in the right parameters. Possibly change the API somehwat.
        encode_call_fn = direct.call_encoding
    else:
        global_encoder_fn = None
        encode_call_fn = None
    config = EncoderConfig(
        structs,
        encode_call_fn,
        global_encoder_fn,
        bounds_by_struct = bounds)
    return encode_ast(config, ast)

def compute_size_bounds(structs, ast):
    consts_by_struct = astutils.consts_by_struct(ast, structs)
    pred_calls = astutils.pred_calls(ast)
    if not pred_calls:
        # No recursive calls, bound is always 0
        logger.info("No predicate calls => Nothing to unfold")
        return { struct : 0 for struct in structs }

    bound_by_struct = { struct : 0 for struct in structs}
    for struct, consts in consts_by_struct.items():
        bound_by_struct[struct] =  _process_struct_consts(struct, consts)
    # Multiply according to which data structure it is
    for struct in bound_by_struct:
        if struct.unqualified_name == consts_mod.LIST_PRED:
            bound_by_struct[struct] *= 2
        elif struct.unqualified_name == consts_mod.TREE_PRED:
            bound_by_struct[struct] *= 4
        else:
            msg = 'Currently no support for bound computation for {}'
            raise utils.SlothException(msg.format(struct))

    # Add number of necessary witnesses depending on pred calls Note:
    # I'm adding these after the multiplicatiion to lower the bound.

    #data_preds = len([p for p in pred_calls if p.pred is not None])
    for p in pred_calls:
        if p.pred is not None:
            num_witnesses = 1 if p.fld is None else 2
            msg = 'Adding {} witnesses to {} because of predicate call {}'
            logger.info(msg.format(num_witnesses, p.struct, p))
            bound_by_struct[p.struct] += num_witnesses

    return bound_by_struct

def _process_struct_consts(struct, consts):
    logger.info("Have the following {} vars: {}".format(struct.name, consts))
    var_count = len(consts)
    if any(z3.eq(v, struct.null) for v in consts):
        logger.info("Will not count null.")
        var_count -= 1
    return var_count

class EncoderConfig:
    def __init__(self, structs, encode_call_fn = None, global_encoder_fn = None, bounds_by_struct = None):
        self.structs = structs
        # From set to avoid duplicate fields (data occurs in every struct!)
        self.flds = list(sorted({f for s in structs for f in s.fields}))
        if structs[0].fp_sort != structs[-1].fp_sort:
            # To ensure this crashes early with the quantified backend
            raise utils.SlothException("Can't use encoder config with quantified backend.")
        self.fp_sort = structs[0].fp_sort
        self.encode_call_fn = encode_call_fn
        self.global_encoder_fn = global_encoder_fn
        self.bounds_by_struct = bounds_by_struct
        self.next_fp_vec_ix = 0
        self.next_fp_ix = 0

    fp_vec_prefix = 'Y'
    fresh_fp_prefix = 'Z'

    def _fp_vec_name(self, i, fld):
        return EncoderConfig.fp_vec_prefix + str(self.next_fp_vec_ix) + fld

    def get_fresh_fpvector(self):
        self.next_fp_vec_ix += 1
        return FPVector(self.fp_sort, self._fp_vec_name(self.next_fp_vec_ix, ''), self.flds)

    def get_fresh_fp(self):
        self.next_fp_ix += 1
        return self.fp_sort[self.fresh_fp_prefix + str(self.next_fp_ix)]


def as_split_constraints(A, B, ast, fresh = None):
    assert isinstance(A, c.SmtConstraint)
    assert isinstance(B, c.SmtConstraint)
    expr = ast.to_sl_expr()
    A.sl_expr = expr
    A.description = 'Structural part (A)'
    B.sl_expr = expr
    B.description = 'Definitional part (B)'
    if fresh is None:
        fresh = set()
    return SplitEnc(A, B, fresh)

def encode_ast(config, ast):
    # TODO: Make 'X' into a constant (see also use below as well as in the conversion of models to graphs)
    X = FPVector(config.fp_sort, 'X', config.flds)
    config.next_fp_ix = 0 # Reset the next free FP id to 0 for consistent naming
    A, B, Z = encode_boolean(config, X, ast)
    A = c.And(A, description = '***** A *****')
    B = c.And(B, description = '***** B *****')
    cs = [A,B]
    if config.global_encoder_fn is not None:
        cs.append(config.global_encoder_fn())
    consts = astutils.consts_by_struct(ast, config.structs)
    dconsts = astutils.data_consts(ast)
    heap_funs = itertools.chain(*(s.heap_fns() for s in config.structs))
    nulls = [struct.null for struct in config.structs]
    decls = set(itertools.chain(Z,
                                X.all_fps(),
                                [config.fp_sort['X']],
                                *consts.values(),
                                dconsts,
                                nulls,
                                heap_funs))
    return c.Z3Input(constraint = c.And(*cs),
                     decls = decls,
                     encoded_ast = ast)

def encode_boolean(config, X, ast):
    type_ = type(ast)
    if type_ is slast.SlAnd:
        return encode_and(config, X, ast)
    elif type_ is slast.SlOr:
        return encode_or(config, X, ast)
    elif type_ is slast.SlNot:
        return encode_not(config, X, ast)
    else:
        Y = config.get_fresh_fpvector()
        A1, B, Z1 = encode_spatial(config, ast, Y)
        connection = c.And(*all_equal(Y, X),
                           description = 'Connecting spatial formula to global constraint')
        A = c.And(A1, connection,
                  description = 'Placing {} in the global context'.format(ast.to_sl_expr()))
        Z = Z1.union(Y.all_fps())
        return SplitEnc(A, B, Z)

def encode_spatial(config, ast, Y):
    type_ = type(ast)
    if type_ == slast.SepCon:
        return encode_sepcon(config, ast, Y)
    elif type_ == slast.PredCall:
        if config.encode_call_fn is None:
            raise utils.SlothException('No call encoder specified')
        else:
            return config.encode_call_fn(config, ast, Y)
    elif type_ == slast.DataAtom:
        return encode_data_atom(ast, Y)
    elif type_ == slast.PointsTo:
        return encode_pto(ast, Y)
    elif type_ == slast.PointsToSingleField:
        return encode_pto_fld(ast, Y)
    elif type_ == slast.SpatialEq:
        return encode_eq(ast, Y)
    else:
        msg = 'No encoder defined for {}'
        raise utils.SlothException(msg.format(type_))

def encode_eq(eq, Y):
    A = c.as_constraint(eq.left == eq.right)
    B = c.And(*(fp.is_empty() for fp in Y.all_fps()))
    return as_split_constraints(A, B, eq)

def encode_data_atom(da, Y):
    A = c.as_constraint(da.atom)
    B = c.And(*(fp.is_empty() for fp in Y.all_fps()))
    return as_split_constraints(A, B, da)

def encode_pto_fld(pto, Y):
    alloced, empty = Y.group_by_flds([pto.fld])
    assert len(alloced) == 1
    struct, src, fld, trg = pto.struct, pto.src, pto.fld, pto.trg
    A = c.And(Not(src == struct.null),
              trg == struct.heap_fn(fld)(src))
    B = c.And(alloced[0].is_singleton(src),
              *(fp.is_empty() for fp in empty))
    return as_split_constraints(A, B, pto)

def encode_pto(pto, Y):
    # TODO: Merge with encode_pto_fld
    struct, src, trgs = pto.struct, pto.src, pto.trg
    flds = struct.points_to_fields
    alloced, empty = Y.group_by_flds(flds)
    assert len(alloced) == len(flds)
    assert len(flds) == len(trgs)
    A = c.And(Not(src == struct.null),
              *(trg == struct.heap_fn(fld)(src) for fld, trg in zip(flds, trgs)))
    B = c.And(*(fp.is_singleton(src) for fp in alloced),
              *(fp.is_empty() for fp in empty))
    return as_split_constraints(A, B, pto)

def all_disjoint(Y1, Y2):
    assert len(Y1) == len(Y2)
    for fld in Y1:
        yield Y1[fld].disjoint_from(Y2[fld])

def all_equal(Y1, Y2):
    assert len(Y1) == len(Y2)
    for fld in Y1:
        yield Y1[fld].is_identical(Y2[fld])

def all_union(Y, Y1, Y2):
    assert len(Y1) == len(Y2) and len(Y) == len(Y1)
    for fld in Y:
        yield Y[fld].union_of(Y1[fld], Y2[fld])

def encode_sepcon(config, sc, Y):
    Y1 = config.get_fresh_fpvector()
    A1, B1, Z1 = encode_spatial(config, sc.left, Y1)
    Y2 = config.get_fresh_fpvector()
    A2, B2, Z2 = encode_spatial(config, sc.right, Y2)

    disjointness = c.And(*all_disjoint(Y1, Y2),
                         description = 'Sepcon operands have disjoint footprints')
    A = c.And(A1, A2, disjointness)

    union = c.And(*all_union(Y, Y1, Y2),
                  description = 'Sepcon operand footprints combine into global footprint')
    B = c.And(B1, B2, union)
    return as_split_constraints(A, B, sc, fresh = Z1.union(Z2).union(Y1.all_fps()).union(Y2.all_fps()))

def encode_binop(op, config, X, ast):
    A1, B1, Z1 = encode_boolean(config, X, ast.left)
    A2, B2, Z2 = encode_boolean(config, X, ast.right)
    A = op(A1, A2)
    B = c.And(B1, B2)
    return as_split_constraints(A, B, ast, fresh = Z1.union(Z2))

encode_and = functools.partial(encode_binop, c.And)
encode_or = functools.partial(encode_binop, c.Or)

def encode_not(config, X, ast):
    A1, B, Z = encode_boolean(config, X, ast.arg)
    A = c.Not(A1)
    return as_split_constraints(A, B, ast, fresh = Z)
