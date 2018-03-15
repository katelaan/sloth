"""Utility functions for interacting with z3 and :class:`z3.ExprRef`.

.. testsetup::

   from z3 import And, Or, Not
   from sloth import *
   from sloth.z3api.z3utils import *

"""

import z3

from .. import consts
from .. import config
from ..utils import utils
from ..utils import logger

###############################################################################
# High-level solver interaction
###############################################################################

_solver = None

def Solver():
    global _solver
    if _solver is None:
        _solver = z3.Solver()
    return _solver

def is_sat(expr):
    _solver.reset()
    _solver.add(expr)
    return sat_solver_state(_solver)

def model():
    return _solver.model()

def sat_solver_state(solver):
    return repr(solver.check()) == "sat"

def unsat_solver_state(solver):
    return repr(solver.check()) == "unsat"

def run_z3(encoding):
    """Run z3 on the given SMT assertion.

    Returns True iff the encoding is satisfiable.

    :param encoding: :class:`z3.ExprRef`, with SL-specific symbols already removed through"""
    s = Solver()
    s.reset()
    s.add(encoding.smt_expr)
    return z3api.z3utils.sat_solver_state(s)

###############################################################################
# Utilities for declarations
###############################################################################

def contains_sort(consts, sort):
    """Does the given list of constants contain a constant of the given sort?"""
    return utils.seq_exists(lambda c : c.decl().range() == sort.ref, consts)

def is_of_sort(c, sort):
    assert(isinstance(sort, z3.SortRef))
    return c.arity() == 0 and c.range() == sort

def decl_to_string(decl):
    assert(isinstance(decl, z3.AstRef))
    if isinstance(decl, z3.FuncDeclRef):
        dom = [str(decl.domain(i)) for i in range(decl.arity())]
        dom_str = " * ".join(dom)
        rng = decl.range()
        return "{} : {} -> {}".format(decl, dom_str, rng)
    else:
        assert(z3.is_const(decl))
        return "{} : {} (const)".format(decl, decl.sort())

def is_array_sort(sort):
    """Returns true iff the given sort reference is an array sort reference"""
    assert(isinstance(sort, z3.SortRef))
    return isinstance(sort, z3.ArraySortRef)

###############################################################################
# Utilities for expression references
###############################################################################

def expr_fold(smt_expr, leaf, inner):
    """Folding the given expression (sexpr tree) by applying the leaf function to each leaf and the inner function at each inner node.

    :param smt_expr: z3 ExprRef
    :param leaf: Function from (constants) ExprRef to rtype
    :param inner: Function from (non-const) ExpRef and list of rtype to rtype
    """
    #logger.info("Folding {}".format(smt_expr))
    assert(isinstance(smt_expr, z3.ExprRef))
    if z3.is_const(smt_expr):
        res = leaf(smt_expr)
        #logger.info("Leaf result for {}: {}".format(smt_expr, res))
        return res
    else:
        folding = [expr_fold(c, leaf, inner) for c in smt_expr.children()]
        # TODO: Why are we returning a list here?
        res = list(inner(smt_expr, folding))
        #logger.info("Folding result from {} into inner result for {}: {}".format(folding, smt_expr, res))
        return res

def partial_expr_fold(smt_expr, is_leaf, leaf, inner):
    """Folding the given expression tree by applying the leaf function to each subtree that satisfies the `is_leaf` predicate, and applying inner further up the tree."""
    assert(isinstance(smt_expr, z3.ExprRef))
    if is_leaf(smt_expr):
        res = leaf(smt_expr)
        #logger.info("Leaf result for {}: {}".format(smt_expr, res))
        return res
    else:
        folding = [partial_expr_fold(c, is_leaf, leaf, inner)
                   for c in smt_expr.children()]
        res = inner(smt_expr, folding)
        #logger.info("Folding result from {} into inner result for {}: {}".format(folding, smt_expr, res))
        return res

def expr_fold_stateful(smt_expr, leaf, inner, update, state):
    assert(isinstance(smt_expr, z3.ExprRef))
    if z3.is_const(smt_expr):
        return leaf(smt_expr, state)
    else:
        folding = [expr_fold_stateful(c, leaf, inner, update, update(state)) for c in smt_expr.children()]
        return inner(smt_expr, folding, state)

keywords = ["True", "False"]

def collect_consts(smt_expr):
    """Returns list of all constants (as ExprRef instances) that appear in the given expression"""
    assert(isinstance(smt_expr, z3.ExprRef))
    non_unique_res = expr_fold(smt_expr,
                     lambda t : [t],
                        lambda _, cs : utils.flatten(cs))
    for c in non_unique_res:
        assert(z3.is_const(c))
    # Leaving the following in, in case conversion breaks again with strange z3 exceptions...
    #logger.info([c.__class__ for c in non_unique_res])
    res = set(non_unique_res)
    #logger.info("Consts in expr: {}".format(res))
    return [c for c in res if str(c) not in keywords]

def contains_const(const, smt_expr):
    """Returns true if `const` occurs in `smt_expr`

    >>> contains_const(sl.beta, Or(sl.alpha == 17, sl.alpha < sl.beta))
    True
    >>> contains_const(sl.beta, And(sl.alpha > 17, sl.alpha < 42))
    False

    """
    return const in collect_consts(smt_expr)

# TODO: Make return types more consistent (not sometimes list, sometimes set; cf. collect_outermost...)
def collect_fun_decls(smt_expr):
    """Return a set of all non-const function declarations that are referenced in the given expression"""
    assert(isinstance(smt_expr, z3.ExprRef))
    res = set(expr_fold(smt_expr,
                     lambda t : [],
                     lambda t, cs : utils.flatten(cs) + [t.decl()]))
    return res #[c for c in res if str(c) not in keywords]

def collect_outermost_theory_decls(smt_expr):
    """Return a set of all non-const theory symbols in the expression that are not themselves arguments to theory symbols"""
    assert(isinstance(smt_expr, z3.ExprRef))

    def fold_inner(t, cs):
        if consts.SL_PREFIX in str(t.decl()):
            # Theory symbol, ignore all its children
            return [t.decl()]
        else:
            # Core symbol, propagate argument symbols
            return utils.flatten(cs) # + [t.decl()]))

    res = set(expr_fold(smt_expr,
                     lambda t : [],
                     fold_inner))
    return res #[c for c in res if str(c) not in keywords]

def by_complexity(c):
    """Key function for sorting constant ExprRef instances.
    Sorting by this function will return SL theory symbols first.
    It will then sort lexicographically for each sort,
    ordering the sorts lexiographically as well,
    returning non-array sorts before array sorts.
    """
    return (0 if "sl." in str(c) else 1,
        1 if is_array_sort(c.decl().range()) else 0,
        str(c.decl()),
        str(c))
