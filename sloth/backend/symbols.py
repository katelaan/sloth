"""Defines all function references (:class:`z3.FuncRef` instances)
for use in the solver.

This includes core symbols such as `and_decl` (for using the `z3.And`
function in a lambda), basic separation logic symbols `sep_con_fn` and
`submodel_fn`, as well as access to backend-specific definitions of
recursive structures in the form of
:class:`sloth.backend.struct.Struct` instances via
:func:`make_predef_structs`.

.. testsetup::

    from sloth import *
    from sloth.backend.symbols import *

"""

import collections
import z3

from .. import consts, config
from ..utils import logger, utils
from ..z3api import z3utils
from . import struct

###############################################################################
# Core SL-independent symbols
###############################################################################

if_decl = z3.If(True, True, True).decl()
or_decl = z3.Or(True, True).decl()
and_decl = z3.And(True, True).decl()
implies_decl = z3.Implies(True, True).decl()
xor_decl = z3.Xor(True, True).decl()
not_decl = z3.Not(True).decl()
Z3True = z3.BoolVal(True)
Z3False = z3.BoolVal(False)

def LAnd(ls):
    """Smart conjunction over a sequence of :class:`z3.ExprRef`.

    Only introduces an `And` for sequences of at least two expressions.

    >>> x, y = z3.Ints("x y")
    >>> LAnd([x == y])
    x == y
    >>> LAnd([x == y, x!= y, x > y])
    And(x == y, x != y, x > y)
    >>> LAnd([])
    True

    """
    l = len(ls)
    if l == 1:
        return ls[0]
    elif l > 1:
        return z3.And(ls)
    else:
        return Z3True

def LOr(ls):
    """Smart disjunction over a sequence of :class:`z3.ExprRef`.

    Only introduces an `Or` for sequences of at least two expressions.

    >>> x, y = z3.Ints("x y")
    >>> LOr([x == y])
    x == y
    >>> LOr([x == y, x!= y, x > y])
    Or(x == y, x != y, x > y)
    >>> LOr([])
    False

    """
    l = len(ls)
    if l == 1:
        return ls[0]
    elif l > 1:
        return z3.Or(ls)
    else:
        return Z3False

def SepCon(ls):
    """Return separating conjunction over sequence of :class:`z3.ExprRef`.

    >>> SepCon([sl.tree("a")])
    sl.tree(a)
    >>> SepCon([sl.tree("a"),sl.tree("b")])
    sl.sepcon(sl.tree(a), sl.tree(b))
    >>> SepCon([sl.tree("a"),sl.tree("b"),sl.tree("c")])
    sl.sepcon(sl.tree(a), sl.sepcon(sl.tree(b), sl.tree(c)))
    >>> SepCon([])
    True

"""
    l = len(ls)
    if l == 0:
        return True
    if l == 1:
        return ls[0]
    else:
        return sep_con_fn(ls[0], SepCon(ls[1:]))

###############################################################################
# General SL theory symbols
###############################################################################

sep_con_fn = z3.Function(consts.SEP_CON, z3.BoolSort(), z3.BoolSort(), z3.BoolSort())
submodel_fn = z3.Function(consts.SUBMODEL, z3.BoolSort(), z3.BoolSort())

# Sorts
data_sort = z3.IntSort() # TODO: Generic data sort?
# TODO: Just keep one of the following two?
data_literal_check = z3.is_int_value
def is_data_const(const):
    assert (z3.is_const(const))
    return z3.eq(const.sort(), data_sort)

# Variables in data predicate
def data_pred_var(i):
    assert(i >= 0 and i < 2)
    if i == 0:
        name = consts.DATA_VAR_ZERO
    else:
        name = consts.DATA_VAR_ONE

    return z3.Const(consts.SL_PREFIX + name, data_sort)
data_vars = [data_pred_var(i) for i in range(consts.MAX_PRED_VARS)]
data_var_decls = { str(v) : v for v in data_vars }

# Map with all background theory declarations
decls = { consts.SEP_CON : sep_con_fn, consts.SUBMODEL : submodel_fn }
decls.update(data_var_decls)
