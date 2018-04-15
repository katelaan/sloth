import z3

from .. import consts as consts_mod
from ..utils import logger, utils
from . import astutils
from . import slast

def compute_size_bounds(ast):
    conj = conjunct_without_calls(ast)
    if conj is not None:
        # TODO: Count pointers instead (no multiplication needed)
        return compute_nondata_bounds(conj)

    bounds = compute_nondata_bounds(ast)
    # Add number of witnesses needed for data predicates
    # TODO: Actually we only need witnesses when the predicate is under negation?
    for struct, preds in astutils.data_preds_by_struct(ast):
        for (fld, _) in preds:
            if fld is None:
                bounds[struct] += 1
            else:
                bounds[struct] += 2
    return bounds

def conjunct_without_calls(ast):
    return None

def compute_nondata_bounds(ast):
    type_ = type(ast)
    if type_ is slast.SlAnd:
        return min(compute_nondata_bounds(ast.left),
                   compute_nondata_bounds(ast.right),
                   key = bound_size_key)
    elif type_ is slast.SlOr:
        return max(compute_nondata_bounds(ast.left),
                   compute_nondata_bounds(ast.right),
                   key = bound_size_key)
    elif type_ is slast.SlNot:
        return compute_nondata_bounds(struct, ast.arg)
    else:
        compute_nondata_bounds_spatial(ast)

def compute_nondata_bounds_spatial(ast):
    consts_by_struct = astutils.consts_by_struct(ast)
    bound_by_struct = {
        struct : _process_struct_consts(struct, consts)
        for struct, consts in consts_by_struct.items()
    }
    # Multiply according to which data structure it is
    for struct in bound_by_struct:
        if struct.unqualified_name == consts_mod.LIST_PRED:
            bound_by_struct[struct] *= 2
        elif struct.unqualified_name == consts_mod.TREE_PRED:
            bound_by_struct[struct] *= 4
        else:
            msg = 'Currently no support for bound computation for {}'
            raise utils.SlothException(msg.format(struct))
    return bound_by_struct

def bound_size_key(bounds):
    return sum(bounds.values())

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
    logger.info("Have the following {} vars: {}".format(struct.name, consts))
    var_count = len(consts)
    if any(z3.eq(v, struct.null) for v in consts):
        logger.info("Will not count null.")
        var_count -= 1
    return var_count
