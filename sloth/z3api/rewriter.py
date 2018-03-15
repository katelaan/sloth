"""Functions for rewriting `z3.ExprRef` syntax trees.

.. testsetup::

   from z3 import And, Or, Not, Ints
   from sloth import *
   from sloth.z3api.rewriter import *

"""

import z3
from z3.z3 import _to_expr_ref as to_expr_ref

from ..utils import logger

def replace_args(t, args):
    """Updates the children of term t with args.
    len(args) must be equal to the number of children in t.
    If t is an application, then len(args) == t.num_args()
    If t is a quantifier, then len(args) == 1
    """
    n = len(args)
    _args = (z3.Ast * n)()
    for i in range(n):
        _args[i] = args[i].as_ast()
    return to_expr_ref(z3.Z3_update_term(t.ctx_ref(), t.as_ast(), n, _args), t.ctx)

def substitute_vars(t, *m):
    """Substitute the free variables in t with the expression in m."""
    # Redefining this here so that the clients of this class aren't forced to
    # import any replacement-related functions directly from z3, thus making
    # it a little easier to add other backends in the future.
    #logger.info("Will substitute into {} arguments {} of sorts {}".format(t, m, map(lambda v : v.sort(), m)))
    return z3.substitute_vars(t, *m)

def conditional_rewrite(s, rewriting_dict,
                        default_fn = replace_args):
    """
    Apply given rewriter to subexpressions of s bottom up
    """
    todo = []
    todo.append(s)
    cache = {}
    while todo:
        n = todo[len(todo) - 1]
        #print(n)
        if z3.is_var(n):
            # No rewriting for variables
            todo.pop()
            cache[n] = default_leaf_fn(n)
        elif z3.is_app(n):
            # Add non-rewritten children to rewriting stack
            processed_all_children = True
            for arg in n.children():
                if arg not in cache:
                    todo.append(arg)
                    processed_all_children = False
            # All children haven been rewritten, so now rewrite n itself
            if processed_all_children:
                todo.pop()
                new_args = [cache[arg] for arg in n.children()]
                enabled_rewriter = rewriting_dict.get(n.decl())
                if enabled_rewriter is not None:
                    #print("Match for {}".format(n.decl()))
                    cache[n] = enabled_rewriter(n, new_args)
                else:
                    #cache[n] = replace_args(n, new_args)
                    cache[n] = default_fn(n, new_args)
        else:
            assert(z3.is_quantifier(n))
            b = n.body()
            if b in cache:
                # The argument of the quantifier has already been rewritten
                # Substitute this rewritten term
                todo.pop()
                cache[n] = replace_args(n, [ cache[b] ])
            else:
                todo.append(b)
    return cache[s]

# TODO: Reduce code duplication (or integrate the two conditional rewriters)
def tagged_conditional_rewrite(s, rewriting_dict, leaf_fn, default_fn):
    """
    Apply given rewriter to subexpressions of s bottom up
    """
    todo = []
    todo.append(s)
    cache = {}
    while todo:
        n = todo[len(todo) - 1]
        #print("Rewriting {}".format(n))
        #print("Current cache: {}".format(cache))
        if z3.is_var(n):
            # No rewriting for variables
            todo.pop()
            # TODO: This is one difference => Could be added as leaf_fn to standard rewrite as well
            cache[n] = leaf_fn(n)
        elif z3.is_app(n):
            # Add non-rewritten children to rewriting stack
            processed_all_children = True
            for arg in n.children():
                if arg not in cache:
                    todo.append(arg)
                    processed_all_children = False
            # All children haven been rewritten, so now rewrite n itself
            if processed_all_children:
                todo.pop()
                new_args = [cache[arg] for arg in n.children()]
                enabled_rewriter = rewriting_dict.get(n.decl())
                if enabled_rewriter is not None:
                    cache[n] = enabled_rewriter(n, new_args)
                else:
                    #cache[n] = replace_args(n, new_args)
                    cache[n] = default_fn(n, new_args)
        else:
            assert(z3.is_quantifier(n))
            b = n.body()
            if b in cache:
                # The argument of the quantifier has already been rewritten
                # Substitute this rewritten term
                todo.pop()
                # TODO: Another difference (but actually not even relevant in our setting). This could also be encapsulated in a function argument which could default to replace_args in the non-tagged setting
                rewritten_arg, tag = cache[b]
                cache[n] = (replace_args(n, [ rewritten_arg ]), tags)
            else:
                todo.append(b)
    return cache[s]




def tree_conditional_rewrite(expr, rewriting_dict,
                        default_fn = replace_args):
    """Rewrite `expr` bottom up, deliberately ignoring sharing in the DAG.

    """
    if z3.is_var(expr):
        return default_leaf_fn(expr)
    elif z3.is_app(expr):
        new_args = [tree_conditional_rewrite(child, rewriting_dict, default_fn)
                    for child in expr.children()]
        enabled_rewriter = rewriting_dict.get(expr.decl())
        if enabled_rewriter is not None:
            #print("Match for {}".format(n.decl()))
            return enabled_rewriter(expr, new_args)
        else:
            return default_fn(expr, new_args)
    else:
        assert(z3.is_quantifier(expr))
        new_arg = tree_conditional_rewrite(expr.body(), rewriting_dict, default_fn)
        return replace_args(expr, new_arg)


def partial_leaf_substitution(expr, substitution_dict):
    """Replaces consts/vars in `expr` according to `substitution_dict`.

    If a const/var is not in `substitution_dict.keys()`, it remains
    unchanged.

    >>> a, b, c = sl.list.locs("a", "b", "c")
    >>> subst = {b : c}
    >>> partial_leaf_substitution(sl.sepcon(sl.list("a"), sl.list("b")), subst)
    sl.sepcon(sl.list(a), sl.list(c))
    >>> i, j = Ints("i j")
    >>> subst = {sl.alpha : i, sl.beta : j}
    >>> partial_leaf_substitution(sl.alpha < sl.beta, subst)
    i < j

    """
    if z3.is_const(expr) or z3.is_var(expr):
        return substitution_dict.get(expr, expr)
    elif z3.is_app(expr):
        new_args = [partial_leaf_substitution(child, substitution_dict)
                    for child in expr.children()]
        return replace_args(expr, new_args)
    else:
        assert(z3.is_quantifier(expr))
        new_arg = partial_leaf_substitution(expr.body(), substitution_dict)
        return replace_args(expr, new_arg)
