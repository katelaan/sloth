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
xor_decl = z3.Xor(True, True).decl()
not_decl = z3.Not(True).decl()

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
        return True

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
        return False

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

###############################################################################
# Predefined predicates
###############################################################################

def make_predef_structs(encoder_backend):
    """
    Instantiate a set of predefined structures with the given backend(s), which specify
    how to parse assertions about the structure and how to generate encodings of the structure.
    By default, we parse using the backend with uninterpreted sorts.
    """
    # TODO: Get rid of dynamic import of backends in symbols module
    from . import backends
    parser_backend = backends.QuantifiedBackend

    list_loc = parser_backend.make_loc_sort(consts.LIST_PRED)
    dlist_loc = parser_backend.make_loc_sort(consts.DLIST_PRED)
    tree_loc = parser_backend.make_loc_sort(consts.TREE_PRED)
    ptree_loc = parser_backend.make_loc_sort(consts.PTREE_PRED)

    list_enc_loc = encoder_backend.make_loc_sort(consts.LIST_PRED)
    dlist_enc_loc = encoder_backend.make_loc_sort(consts.DLIST_PRED)
    tree_enc_loc = encoder_backend.make_loc_sort(consts.TREE_PRED)
    ptree_enc_loc = encoder_backend.make_loc_sort(consts.PTREE_PRED)

    Rule = struct.Rule
    Ptr = struct.Ptr

    # TODO: Allocate data pointers in unrolling rules? -- See also FIXME in unrolling_rewriter in rewriting

    list_struct = struct.Struct(consts.LIST_PRED,
                        input_sort_name = str(list_loc),
                        sort = list_enc_loc,
                        fields = {consts.FLD_NEXT : list_enc_loc.ref,
                                  consts.FLD_DATA : data_sort},
                        structural_fields = [consts.FLD_NEXT],
                        points_to_fields = [consts.FLD_NEXT],
                        unrolling_rules = [
                            Rule([Ptr(0, 1, consts.FLD_NEXT)])
                        ],
                        LocInterpretation = encoder_backend.LocInterpretation
    )
    dlist_struct = struct.Struct(consts.DLIST_PRED,
                          input_sort_name = str(dlist_loc),
                          sort = dlist_enc_loc,
                          fields = {consts.FLD_NEXT : dlist_enc_loc.ref,
                                    consts.FLD_PREV : dlist_enc_loc.ref,
                                    consts.FLD_DATA : data_sort},
                          structural_fields = [consts.FLD_NEXT],
                          points_to_fields = [consts.FLD_NEXT, consts.FLD_PREV],
                          unrolling_rules = [
                              Rule([Ptr(0, 1, consts.FLD_NEXT), Ptr(1, 0, consts.FLD_PREV)]),
                              Rule([Ptr(0, 1, consts.FLD_NEXT)], force_null = [1])
                          ],
                          LocInterpretation = encoder_backend.LocInterpretation
    )
    tree_struct = struct.Struct(consts.TREE_PRED,
                         input_sort_name = str(tree_loc),
                         sort = tree_enc_loc,
                         fields = {consts.FLD_LEFT : tree_enc_loc.ref,
                                   consts.FLD_RIGHT : tree_enc_loc.ref,
                                   consts.FLD_DATA : data_sort},
                         structural_fields = [consts.FLD_LEFT, consts.FLD_RIGHT],
                         points_to_fields = [consts.FLD_LEFT, consts.FLD_RIGHT],
                         unrolling_rules = [
                             Rule([Ptr(0, 1, consts.FLD_LEFT), Ptr(0, 2, consts.FLD_RIGHT)])
                         ],
                         LocInterpretation = encoder_backend.LocInterpretation
    )
    ptree_struct = struct.Struct(consts.PTREE_PRED,
                          input_sort_name = str(ptree_loc),
                          sort = ptree_enc_loc,
                          fields = {consts.FLD_LEFT : ptree_enc_loc.ref,
                                    consts.FLD_RIGHT : ptree_enc_loc.ref,
                                    consts.FLD_PARENT : ptree_enc_loc.ref,
                                    consts.FLD_DATA : data_sort},
                          structural_fields = [consts.FLD_LEFT, consts.FLD_RIGHT],
                          points_to_fields = [consts.FLD_LEFT, consts.FLD_RIGHT, consts.FLD_PARENT],
                          unrolling_rules = [
                              # Both children non-null
                              Rule([Ptr(0, 1, consts.FLD_LEFT), Ptr(1, 0, consts.FLD_PARENT),
                                    Ptr(0, 2, consts.FLD_RIGHT), Ptr(2, 0, consts.FLD_PARENT)
                              ]),
                              # Left child non-null
                              Rule([Ptr(0, 1, consts.FLD_LEFT), Ptr(1, 0, consts.FLD_PARENT),
                                    Ptr(0, 2, consts.FLD_RIGHT)],
                                   force_null = [2]),
                              # Right child non-null
                              Rule([Ptr(0, 1, consts.FLD_LEFT),
                                    Ptr(0, 2, consts.FLD_RIGHT), Ptr(2, 0, consts.FLD_PARENT)],
                                   force_null = [1]),
                              # Both children null
                              Rule([Ptr(0, 1, consts.FLD_LEFT),
                                    Ptr(0, 2, consts.FLD_RIGHT)],
                                   force_null = [1,2])
                          ],
                          LocInterpretation = encoder_backend.LocInterpretation
    )

    # Recursive predicates
    predef = [list_struct, dlist_struct, tree_struct, ptree_struct]
    return predef

###############################################################################
# Auxiliary functions for structures
###############################################################################

def spatial_symbols(structs):
    """Returns a set of all defined spatial SL theory symbols.

    The set contains both the symbols for the given structures and the
    built-in symbols.

    """
    all_decls = [struct.spatial_decls() for struct in structs]
    return set(utils.flatten(all_decls) + [sep_con_fn, submodel_fn])

def is_root_of_struct(structs, expr):
    """Return true iff the given expression is a predicate (segment) call for one of the predefined structures."""
    assert(isinstance(expr, z3.ExprRef))
    for struct in structs:
        if expr.decl() in struct.recursive_predicates():
            logger.debug("{} is root of {}".format(expr, struct.name))
            return True
    return False

def is_root_of(struct, expr):
    assert(isinstance(struct, Struct))
    assert(isinstance(expr, z3.ExprRef))
    return expr.decl() in struct.parsable_decls()

def print_sl_summary(structs):
    for s in structs:
        print_struct_summary(s)

def print_struct_summary(struct):
    print("STRUCT {} [".format(struct))
    print("  location sort for input = {}".format(struct.input_sort_name))
    print("  location sort in encoding = {}".format(struct.sort))
    to_print = [z3utils.decl_to_string(decl) for decl in struct.parsable_decls()]
    for v in sorted(to_print):
        print("  " + v)
    print("]")
