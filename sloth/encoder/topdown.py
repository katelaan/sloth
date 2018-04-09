"""Encoding of non-call SL formulas.

.. testsetup:

   from sloth import *
   from sloth.encoder.topdown import *

We test the encoder for formulas that do not contain calls. Formulas
with calls are tested separately for each call encoding.

>>> sts = sl.structs
>>> config = EncoderConfig()

"""


import functools

from z3 import And, Not, Or

from . import constraints as c
from . import slast
from .shared import *

def as_split_constraints(A, B, ast, fresh = None):
    expr = ast.to_sl_expr()
    A.sl_expr = expr
    A.description = 'Structural part (A)'
    B.sl_expr = expr
    B.description = 'Definitional part (B)'
    if fresh is None:
        fresh = set()
    return SplitEnc(A, B, fresh)

class EncoderConfig:
    def __init__(self, call_encoder_fn = None, global_encoder_fn = None, bounds_by_struct = None):
        self.call_encoder_fn = call_encoder_fn
        self.global_encoder_fn = global_encoder_fn
        self.bounds_by_struct = bounds_by_struct

def fresh(used):
    pass

def encode_ast(config, ast):
    A, B, Z = encode_boolean(config, set(), ast)
    cs = [A,B]
    if config.global_encoder is not None:
        cs.append(config.global_encoder())
    return c.And(*cs)

def encode_boolean(config, used_fps, ast):
    type_ = type(ast)
    if type_ is encoder.SlAnd:
        return encode_and(config, used_fps, ast)
    elif type_ is encoder.SlOr:
        return encode_or(config, used_fps, ast)
    elif type_ is encoder.SlNot:
        return encode_not(config, used_fps, ast)
    else:
        Y = fresh(used_fps)
        return encode_spatial(config, ast, Y)

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
    assert len(flds) == len(trg)
    A = c.And(Not(src == struct.null),
              *(trg == struct.heap_fn(fld)(src) for fld, trg in zip(flds, trgs)))
    B = c.And(*(fp.is_singleton(src) for fp in alloced),
              *(fp.is_empty() for fp in empty))
    return as_split_constraints(A, B, pto)

def all_disjoint(Y1, Y2):
    assert len(Y1) == len(Y2)
    for fld in Y1:
        yield Y1[fld].disjoint_from(Y2[fld])

def all_union(Y, Y1, Y2):
    assert len(Y1) == len(Y2) and len(Y) == len(Y1)
    for fld in Y:
        yield Y[fld].union_of(Y1[fld], Y2[fld])

def encode_sepcon(sc, config, Y):
    used = set(Y.all_fps())
    Y1 = fresh(used)
    A1, B1, Z1 = encode_spatial(sc.left, config, Y1)
    used.update(Z1)
    Y2 = fresh(used)
    A2, B2, Z2 = encode_spatial(sc.right, config, Y2)

    disjointness = c.And(*all_disjoint(Y1, Y2),
                         description = 'Sepcon operands have disjoint footprints')
    A = c.And(A1, A2, disjointness)

    union = c.And(*all_union(Y, Y1, Y2),
                  description = 'Sepcon operand footprints combine into global footprint')
    B = c.And(B1, B2, union)
    return as_split_constraints(A, B, sc, fresh = Z1.union(Z2).union(Y1).union(Y2))

encode_and = functools.partial(encode_binop, c.And)
encode_or = functools.partial(encode_binop, c.Or)

def encode_binopop(op, config, used_fps, ast):
    A1, B1, Z1 = encode_boolean(config, used_fps, ast.left)
    used_fps = used_fps.union(Z1)
    A2, B2, Z2 = encode_boolean(config, used_fps, ast.right)
    A = op(A1, A2)
    B = c.And(B1, B2)
    return as_split_constraints(A, B, ast, fresh = Z1.union(Z2))

def encode_not(config, used_fps, ast):
    A1, B, Z = encode_boolean(config, used_fps, ast.arg)
    A = c.Not(A1)
    return as_split_constraints(A, B, ast, fresh = Z)
