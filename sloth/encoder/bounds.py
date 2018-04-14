import z3

from .. import consts as consts_mod
from ..utils import logger, utils
from . import astutils

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
