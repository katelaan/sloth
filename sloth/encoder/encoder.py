import functools

from ..utils import logger
from . import astbuilder
from . import astutils
from . import bounds as b
from . import direct
from . import shared
from . import translation

from ..z3api import z3utils

def encode_sl_expr(sl, sl_expr, override_bound = None):
    structs = z3utils.structs_in_expr(sl, sl_expr)
    ast = astbuilder.ast(structs, sl_expr)
    #bounds = b.paper_size_bounds(ast)
    bounds = b.compute_size_bounds(ast)
    if override_bound is not None:
        bounds = {s : override_bound for s in bounds}
    # TODO: Can we have one set of fresh variables and one delta formula per struct? Meaning that we can encode lists and trees separately?
    n = sum(bounds.values())
    if astutils.contains_calls(ast):
        if n == 0:
            logger.info('have a call => manually force the bound to be at least 1')
            bounds = {s : 1 for s in bounds}
            n = len(bounds)

        if override_bound is not None:
            note = ' [MANUAL OVERRIDE]'
        else:
            note = ''
        logger.info('Computed bounds: {}{}'.format(bounds, note))
        # TODO: Get rid of the explicit sort in the direct encoder API
        global_encoder_fn = functools.partial(direct.is_bounded_heap_interpretation, n, structs)
        # TODO: Ensure we pass in the right parameters. Possibly change the API somehwat.
        encode_call_fn = direct.call_encoding
    else:
        global_encoder_fn = None
        encode_call_fn = None
    config = EncoderConfig(
        structs,
        encode_call_fn,
        global_encoder_fn,
        bounds_by_struct = bounds)
    return translation.encode_ast(config, ast)

class EncoderConfig:
    def __init__(self, structs, encode_call_fn = None, global_encoder_fn = None, bounds_by_struct = None):
        self.structs = structs
        # From set to avoid duplicate fields (data occurs in every struct!)
        self.flds = list(sorted({f for s in structs for f in s.fields}))
        if structs[0].fp_sort != structs[-1].fp_sort:
            # To ensure this crashes early with the quantified backend
            raise utils.SlothException("Can't use encoder config with quantified backend.")
        self.fp_sort = structs[0].fp_sort
        self.encode_call_fn = encode_call_fn
        self.global_encoder_fn = global_encoder_fn
        self.bounds_by_struct = bounds_by_struct
        self.next_fp_vec_ix = 0
        self.next_fp_ix = 0

    fp_vec_prefix = 'Y'
    fresh_fp_prefix = 'Z'

    def _fp_vec_name(self, i, fld):
        return EncoderConfig.fp_vec_prefix + str(self.next_fp_vec_ix) + fld

    def get_fresh_fpvector(self):
        self.next_fp_vec_ix += 1
        return shared.FPVector(self.fp_sort, self._fp_vec_name(self.next_fp_vec_ix, ''), self.flds)

    def get_fresh_fp(self):
        self.next_fp_ix += 1
        return self.fp_sort[self.fresh_fp_prefix + str(self.next_fp_ix)]
