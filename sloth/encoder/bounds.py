""".. testsetup::

   from sloth import *
   from sloth.encoder.astbuilder import ast
   from sloth.encoder.bounds import *

>>> t = ast(sl.structs, sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z'), sl.tree.left('t', 'u'), sl.tree.right('t','v'), sl.tree.pointsto('u', 'w1', 'w2'))); utils.print_unique_repr(compute_size_bounds(t))
{Struct(sl.list): 1, Struct(sl.tree): 2}
>>> t = ast(sl.structs, z3.And(sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z')), z3.Not(sl.list.pointsto('z', 'y')))); compute_size_bounds(t)
{Struct(sl.list): 1}
>>> t = ast(sl.structs, sl.sepcon(sl.list('x'), sl.list('y'), sl.tree.seg('t','u'))); utils.print_unique_repr(compute_size_bounds(t))
{Struct(sl.list): 4, Struct(sl.tree): 4}

Same bound even with data predicate, because the predicate occurs in a
positive spatial formula, so we do not need witnesses for the
predicates falsity:

>>> t = ast(sl.structs, sl.sepcon(sl.list('x'), sl.list('y'), sl.tree.dpred.left1(sl.alpha < sl.beta, 't', 'u'))); utils.print_unique_repr(compute_size_bounds(t))
{Struct(sl.list): 4, Struct(sl.tree): 4}

If the call is under negation, we add 2 for the witnesses.

>>> t = ast(sl.structs, z3.Not(sl.sepcon(sl.list('x'), sl.list('y'), sl.tree.dpred.left1(sl.alpha < sl.beta, 't', 'u')))); utils.print_unique_repr(compute_size_bounds(t))
{Struct(sl.list): 4, Struct(sl.tree): 6}

If there are multiple branches, we use the larger "basic" bound (bound
prior to adding witnesses):

>>> t = ast(sl.structs, z3.And(sl.sepcon(sl.list('x'), sl.list('y'), sl.tree.dpred.left1(sl.alpha < sl.beta, 't', 'u')), z3.Not(sl.sepcon(sl.list('x'), sl.list('y'), sl.tree.dpred.left1(sl.alpha < sl.beta, 't', 'u'))))); utils.print_unique_repr(compute_size_bounds(t))
{Struct(sl.list): 4, Struct(sl.tree): 6}

"""

import z3

from .. import consts as consts_mod
from ..utils import logger, utils
from . import astutils
from . import slast

def compute_size_bounds(ast):
    """Compute per-structure size bounds for the given :class:`sloth.encoder.SlAst` `ast`.

    For usage info, see the module docstring.

    """
    bounds = noncall_conjunct_bounds(ast)
    if bounds is not None:
        # There's a top-level conjunct without calls - that gives us a strict upper bound on the size!
        #logger.info('Top-level conjunct without calls => Shortcircuiting bound computation')
        logger.debug('Top-level conjunct without calls => Shortcircuiting bound computation')
        return bounds
    else:
        bounds = compute_nondata_bounds(ast)
        logger.debug('Bounds without considering data predicate witnesses: {}'.format(bounds))
        # Add number of witnesses needed for data predicates
        # Note: We only need witnesses for the *falsity* of predicates that *must* be false,
        # i.e., for data predicates that are under negation!
        for atom, is_negated in astutils.atoms_with_polarity(ast):
            if is_negated and atom.is_pred_call() and atom.pred is not None:
                if atom.fld is None:
                    logger.debug('Unary pred {} under negation for {} => bound+=1'.format(atom.pred, atom.struct))
                    bounds[atom.struct] += 1
                else:
                    logger.debug('Binary {}-pred {} under negation for {} => bound+=2'.format(atom.fld, atom.pred, atom.struct))
                    bounds[atom.struct] += 2
        return bounds

def noncall_conjunct_bounds(ast):
    """Compute the size bound based on the allocation in a top-level conjunct without calls.

    If there is no such top-level conjunct, return `None`.

    >>> t = ast(sl.structs, sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z'), sl.tree.left('t', 'u'), sl.tree.right('t','v'), sl.tree.pointsto('u', 'w1', 'w2'))); utils.print_unique_repr(noncall_conjunct_bounds(t))
    {Struct(sl.list): 1, Struct(sl.tree): 2}

    """

    conj_it = conjuncts_without_calls(ast)
    try:
        conj = next(conj_it)
    except:
        # No conjunction without calls -- that's fine, compute regular bounds
        return None
    else:
        logger.debug('Shortcircuiting on {}'.format(conj))
        # There is a top-level conjunct without calls
        # => Count number of allocated consts to get bound
        alloced = ((atom.struct, atom.src) for atom in astutils.atoms(conj)
                   if hasattr(atom, 'src'))
        by_struct = {}
        for struct, src in alloced:
            by_struct.setdefault(struct, set()).add(src)

        # Force that the bound is set to at least 0 (which otherwise
        # wouldn't the case for formulas without allocation.)
        for struct in astutils.structs_in_ast(ast):
            by_struct.setdefault(struct, set())

        logger.debug('Collected allocation: {}'.format(by_struct))
        return {struct : len(cs) for struct, cs in by_struct.items()}

def conjuncts_without_calls(ast):
    """Generate all top-level conjuncts of `ast` that don't contain any predicate calls.

    >>> t = ast(sl.structs, z3.And(sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z')), z3.Not(sl.list.pointsto('z', 'y')))); list(conjuncts_without_calls(t))
    [SepCon(PointsTo('sl.list', x, y), SpatialEq(x, z, False))]

    """
    type_ = type(ast)
    if type_ is slast.SlAnd:
        yield from conjuncts_without_calls(ast.left)
        yield from conjuncts_without_calls(ast.right)
    elif type_ in (slast.SlOr, slast.SlNot):
        # We're only interested in top-level conjuncts
        # (Conjuncts that *must* hold to make the formula true)
        pass
    else:
        # ast is a spatial formula. Check if one of the atoms is a call
        for atom in astutils.atoms(ast):
            if atom.is_pred_call():
                break;
        else:
            # No atom is a predicate call
            yield ast

def compute_nondata_bounds(ast):
    type_ = type(ast)
    if type_ is slast.SlAnd:
        return max_by_struct(compute_nondata_bounds(ast.left),
                             compute_nondata_bounds(ast.right))
    elif type_ is slast.SlOr:
        return max_by_struct(compute_nondata_bounds(ast.left),
                             compute_nondata_bounds(ast.right))
    elif type_ is slast.SlNot:
        return compute_nondata_bounds(ast.arg)
    else:
        return compute_nondata_bounds_spatial(ast)

def compute_nondata_bounds_spatial(ast):
    consts_by_struct = astutils.consts_by_struct(ast)
    bound_by_struct = {
        struct : _process_struct_consts(struct, consts)
        for struct, consts in consts_by_struct.items()
    }
    logger.debug('Lower bound for size bound: #consts = {}'.format(bound_by_struct))
    # Add induction indicators + LCAs
    for atom in astutils.atoms(ast):
        if atom.is_pred_call():
            struct = atom.struct
            name = struct.unqualified_name
            if name == consts_mod.LIST_PRED:
                # One induction indicator
                essential = 1
                bound_by_struct[struct] += essential
            elif name == consts_mod.TREE_PRED:
                # 2 induction indicators + (k-1) LCAs
                # FIXME: Shouldn't we at least add the two induction indicators for trees -- even if there are no stop nodes whatsoever?
                essential = 1 + len(atom.stop_nodes)
                bound_by_struct[struct] += essential
            else:
                msg = 'Currently no support for bound computation for {}'
                raise utils.SlothException(msg.format(struct))
            logger.debug('Added {} for predicate call {}'.format(essential, atom))

    return bound_by_struct

def max_by_struct(left, right):
    return {struct : max(left.get(struct, 0), right.get(struct, 0))
            for struct in set(left).union(right)}


def paper_size_bounds(ast):
    pred_calls = astutils.pred_calls(ast)
    if not pred_calls:
        # No recursive calls, bound is always 0
        logger.info("No predicate calls => Nothing to unfold")
        return {}

    bound_by_struct = compute_nondata_bounds_spatial(ast)

    # Add number of necessary witnesses depending on pred calls Note:
    # I'm adding these after the multiplication to lower the bound.

    #data_preds = len([p for p in pred_calls if p.pred is not None])
    for p in pred_calls:
        if p.pred is not None:
            num_witnesses = 1 if p.fld is None else 2
            msg = 'Adding {} witnesses to {} because of predicate call {}'
            logger.info(msg.format(num_witnesses, p.struct, p))
            bound_by_struct[p.struct] += num_witnesses

    return bound_by_struct

def _process_struct_consts(struct, consts):
    logger.debug("Have the following {} vars: {}".format(struct.name, consts))
    var_count = len(consts)
    if any(z3.eq(v, struct.null) for v in consts):
        logger.info("Will not count null.")
        var_count -= 1
    return var_count
