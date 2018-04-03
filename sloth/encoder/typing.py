"""Implementation of various typing / preprocessing passes used in
the encoding.

.. testsetup::

  from sloth.api import *
  from sloth.z3api import rewriter
  from sloth.encoder.typing import *

"""

from z3 import eq, FuncDeclRef, Var, BoolSort, And

from ..utils import logger, utils
from ..z3api import z3utils, rewriter
from ..backend import symbols, struct
from .exceptions import SortMixException, UndefinedStructException, PureSpatialMixException

def struct_of(decl, structs, tolerate_failure = False):
    """Return the structure which declares the given declaration.

    If none of the given structures declares `decl`, raise an
    exception or, if `tolerate_failure==True`, return None.

    """
    for struct in structs:
        if decl in struct.parsable_decls() + list(struct.sorted_versions()):
            return struct

    if not tolerate_failure:
        # TODO: Catch this exception somewhere?
        fmt = "Argument '{}' does not match any predefined structure"
        raise UndefinedStructException(fmt.format(decl))

def separate_spatial_pure(expr, structs):
    """Separates the given expression into its pure and spatial parts.

    Raises a :class:`exceptions.PureSpatialMixEception` exception if no neat
    separation is possible (because pure and spatial formulas are
    mixed below disjunction or negation).
    """
    bool_decls = {symbols.and_decl, symbols.or_decl, symbols.not_decl}
    def is_leaf(smt_expr):
        return smt_expr.decl() not in bool_decls
    def leaf(smt_expr):
        if smt_expr.decl() in struct.spatial_symbols(structs):
            return (None, smt_expr)
        else:
            return (smt_expr, None)
    def inner(smt_expr, children):
        pure, spatial = zip(*children)
        nontrivial_pure = [p for p in pure if p is not None]
        nontrivial_spatial = [s for s in spatial if s is not None]
        assert(nontrivial_pure or nontrivial_spatial)
        if nontrivial_spatial and nontrivial_pure:
            if not eq(smt_expr.decl(), symbols.and_decl):
                fmt = "Mixing spatial and pure assertions below {} is not supported."
                raise PureSpatialMixException(fmt.format(smt_expr.decl()))
            else:
                return (symbols.LAnd(nontrivial_pure),
                        symbols.LAnd(nontrivial_spatial))
        else:
            if nontrivial_pure:
                return (smt_expr, None)
            else:
                return (None, smt_expr)
    return z3utils.partial_expr_fold(expr, is_leaf, leaf, inner)


def assign_sepcon_sorts(structs):
    """Replace separating conjunctions by sorted separating conjunctions
    based on the sorts in its arguments, failing if there is no unique
    sort that can be assigned.

    >>> rew = assign_sepcon_sorts([sl.list.struct])
    >>> rewriter.conditional_rewrite(sl.sepcon(sl.list("a"), sl.list("b")), rew)
    sl.list.sepcon(sl.list(a), sl.list(b))

    """
    return assign_sort_to_predicate(structs, symbols.sep_con_fn, "Separating conjunction")

def assign_sorts_to_boolean_closure(structs):
    """Replaces Boolean operators and submodel predicates by typed
versions where possible.

    >>> rew = assign_sorts_to_boolean_closure([sl.list.struct])
    >>> rewriter.conditional_rewrite(z3.And(sl.list("a"), sl.list("b")), rew)
    sl.list.conj(sl.list(a), sl.list(b))

    """
    return utils.merge_dicts(
        assign_sort_to_predicate(structs, symbols.submodel_fn, "Submodel predicate"),
        # For the Boolean operators we continue even if we can't type their arguments
        # A separate pass will ensure this only happens if the arguments are pure formulas
        assign_sort_to_predicate(structs, symbols.not_decl, "Negation", tolerate_failure = True),
        assign_sort_to_predicate(structs, symbols.and_decl, "Classical conjunction", tolerate_failure = True),
        assign_sort_to_predicate(structs, symbols.or_decl, "Classical disjunction", tolerate_failure = True)
    )

def assign_sort_to_predicate(structs, pred, desc, tolerate_failure = False):
    """Replaces predicate by its sorted version based on the sorts in its
arguments, failing if there is no unique sort that can be assigned.

    """
    assert(isinstance(pred, FuncDeclRef))
    assert(pred.range() == BoolSort())

    def rewrite(t, cs):
        logger.info("Attempting rewrite of {} with children {}".format(t, cs))
        child_structs = set(struct_of(c.decl(), structs, tolerate_failure) for c in cs)
        s = list(child_structs)[0]
        if len(child_structs) != 1 or s is None:
            if not tolerate_failure:
                fmt = "{} applied to untyped terms or terms of different sorts: {}"
                raise SortMixException(fmt.format(desc,cs))
            else:
                fmt = "Skipping rewrite of {}, typing children {} impossible"
                logger.debug(fmt.format(desc,cs))
                fun_decl = pred
        else:
            fun_decl = s.sorted_version(pred)

        return fun_decl(*cs)

    return {pred : rewrite}

def make_vararg_ops_binary_rewriter():
    """Turns conjunctions/disjunctions that are applied to more than two
arguments into nested binary applications.

    >>> rew = make_vararg_ops_binary_rewriter()
    >>> rewriter.conditional_rewrite(z3.And(sl.list("a"), sl.list("b"), sl.list("c")), rew)
    And(sl.list(a), And(sl.list(b), sl.list(c)))

    """
    # TODO: Logarithmic instead of linear depth for more readable pretty printing
    def rec_rewrite(decl, remainder):
        if len(remainder) == 2:
            return decl(remainder[0], remainder[1])
        else:
            return decl(remainder[0], rec_rewrite(decl, remainder[1:]))

    def rewrite(t, cs):
        if len(cs) > 2:
            logger.debug("Turning {} with {} children into sequence of binary applications".format(t, cs))
        return rec_rewrite(t.decl(), cs)

    return {symbols.and_decl : rewrite, symbols.or_decl : rewrite}

def make_vararg_ops_binary(expr):
    return rewriter.conditional_rewrite(expr, make_vararg_ops_binary_rewriter())

def check_typedness(structs):
    """Rewriter for checking whether a given expression is well-typed,
    i.e., does not mix different sorts or have untyped operands below
    Boolean operands.

    >>> rew = check_typedness(sts)
    >>> rewriter.conditional_rewrite(z3.And(sl.list("a"), sl.tree("b")), rew)
    Traceback (most recent call last):
    ...
    SortMixException: And applied to children of different sorts, [sl.list(a), sl.tree(b)]

    """
    def child_types(t, ignore_decls):
        funs = z3utils.collect_outermost_theory_decls(t) - ignore_decls
        logger.debug("Children of {}: {}".format(t, funs))
        sorts = {struct_of(f, structs, tolerate_failure = True) for f in funs} - {None}
        logger.debug("Sorts: {}".format(", ".join(map(str,sorts))))
        return sorts

    decls_to_ignore = {s.sorted_version(symbols.submodel_fn) for s in structs}

    def is_well_typed(t):
        # Different child sorts are only allowed if they are encapsulated in submodels
        # After excluding submodels,
        # 1 sort is ok (consistent spatial args), 0 is ok (only pure args)
        return len(child_types(t, decls_to_ignore)) <= 1

    def rewrite(t, cs):
        if is_well_typed(t):
            # No rewriting necessary
            # This pass only checks if everything has been typed consistently
            return t
        else:
            fmt = "{} applied to children of different sorts, {}"
            raise SortMixException(fmt.format(t.decl(), cs))

    # Match untyped Boolean operators (everything else is typed at this point)
    return { decl : rewrite for decl in [symbols.and_decl, symbols.or_decl, symbols.not_decl] }
