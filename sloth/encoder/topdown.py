"""Encoding of non-call SL formulas.

.. testsetup::

   from sloth import *
   from sloth.z3api import *
   from sloth.encoder import astbuilder
   from sloth.encoder.topdown import *

We test the encoder for formulas that do not contain calls. Formulas
with calls are tested separately for each call encoding.

>>> sts = [sl.list.struct, sl.tree.struct]; config = EncoderConfig(sts); as_ast = astbuilder.ast


"""

import functools

from z3 import And, Not, Or

from ..utils import utils
from . import constraints as c
from . import slast
from .shared import *

class EncoderConfig:
    def __init__(self, structs, call_encoder_fn = None, global_encoder_fn = None, bounds_by_struct = None):
        self.structs = structs
        # From set to avoid duplicate fields (data occurs in every struct!)
        self.flds = list(sorted({f for s in structs for f in s.fields}))
        if structs[0].fp_sort != structs[-1].fp_sort:
            # To ensure this crashes early with the quantified backend
            raise utils.SlothException("Can't use encoder config with quantified backend.")
        self.fp_sort = structs[0].fp_sort
        self.call_encoder_fn = call_encoder_fn
        self.global_encoder_fn = global_encoder_fn
        self.bounds_by_struct = bounds_by_struct
        self.next_fp_ix = 0

    prefix = 'Y'

    def _fp_name(self, i, fld):
        return EncoderConfig.prefix + str(self.next_fp_ix) + fld

    def get_fresh_fpvector(self):
        self.next_fp_ix += 1
        return FPVector(self.fp_sort, self._fp_name(self.next_fp_ix, ''), self.flds)


def as_split_constraints(A, B, ast, fresh = None):
    expr = ast.to_sl_expr()
    A.sl_expr = expr
    A.description = 'Structural part (A)'
    B.sl_expr = expr
    B.description = 'Definitional part (B)'
    if fresh is None:
        fresh = set()
    return SplitEnc(A, B, fresh)

def encode_ast(config, ast):
    X = FPVector(config.fp_sort, 'X', config.flds)
    config.next_fp_ix = 0 # Reset the next free FP id to 0 for consistent naming
    A, B, Z = encode_boolean(config, X, ast)
    cs = [A,B]
    if config.global_encoder_fn is not None:
        cs.append(config.global_encoder_fn())
    # TODO: Is it correct to include the global constraint in Z?
    return c.Z3Input(constraint = c.And(*cs),
                     decls = Z.union(X.all_fps()),
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
        A = c.And(A1, *all_equal(Y, X),
                  description = 'Connecting spatial formula to global constraint')
        Z = Z1.union(Y.all_fps())
        return SplitEnc(A, B, Z)

def encode_spatial(config, ast, Y):
    type_ = type(ast)
    if type_ == slast.SepCon:
        return encode_sepcon(config, ast, Y)
    elif type_ == slast.PredCall:
        return config.global_encoder_fn(config, ast, Y)
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
    A = eq.left == eq.right
    B = And(*(fp.is_empty() for fp in Y.all_fps()))
    return as_split_constraints(A, B, eq)

def encode_data_atom(da, Y):
    A = da.atom
    B = And(*(fp.is_empty() for fp in Y.all_fps()))
    return as_split_constraints(A, B, da)

def encode_pto_fld(pto, Y):
    alloced, empty = Y.group_by_flds([pto.fld])
    assert len(alloced) == 1
    struct, src, fld, trg = ptro.struct, pto.src, pto.fld, pto.trg
    A = c.And(Not(src == struct.null),
              trg == struct.heap_fn(fld)(src),
              ast = pto,
              a_or_b = _A)
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
