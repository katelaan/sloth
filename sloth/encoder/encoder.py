"""

.. testsetup::

   from sloth import *
   from sloth.encoder.encoder import *

"""

import functools

import z3

from ..backend import lambdas
from ..backend import symbols
from ..utils import logger
from ..z3api import z3utils
from . import astbuilder
from . import astutils
from . import bounds as b
from . import constraints as c
from . import direct
from . import shared
from . import slast
from . import translation

def encode_sl_expr(sl, sl_expr, override_bound = None):
    structs = z3utils.structs_in_expr(sl, sl_expr)
    ast = astbuilder.ast(structs, sl_expr)
    contains_call = astutils.contains_calls(ast)

    bounds = b.compute_size_bounds(ast)
    note = ''

    if override_bound is not None:
        bounds = {s : override_bound for s in bounds}
        note = ' [MANUAL OVERRIDE]'

    if contains_call and sum(bounds.values()) == 0:
        logger.info('Have a call => manually force the bound to be at least 1')
        bounds = {s : 1 for s in bounds}
        note = ' [CALL OVERRIDE]'

    logger.info('Computed bounds: {}{}'.format(bounds, note))

    config = EncoderConfig(bounds_by_struct = bounds)

    if contains_call:
        config.global_encoder_fn = direct.is_bounded_heap_interpretation
        config.encode_call_fn = direct.call_encoding

    return translation.encode_ast(config, ast)

class EncoderConfig:

    fp_vec_prefix = 'Y'
    fresh_fp_prefix = 'Z'
    reach_fun_prefix = 'r'

    def __init__(self, bounds_by_struct, encode_call_fn = None, global_encoder_fn = None):
        self.structs = list(sorted(bounds_by_struct, key = lambda s: s.name))
        # From set to avoid duplicate fields (data occurs in every struct!)
        self.flds = list(sorted({f for s in self.structs for f in s.fields}))
        if self.structs:
            if self.structs[0].fp_sort != self.structs[-1].fp_sort:
                # To ensure this crashes early with the quantified backend
                raise utils.SlothException("Can't use encoder config with quantified backend.")
            self.sort = self.structs[0].sort
            self.fp_sort = self.structs[0].fp_sort
        else:
            self.sort = None
            self.fp_sort = None
        self.encode_call_fn = encode_call_fn
        self.global_encoder_fn = global_encoder_fn
        self.bounds_by_struct = bounds_by_struct
        self.n = sum(bounds_by_struct.values())
        self.next_fp_vec_ix = 0
        self.next_fp_ix = 0
        self.next_r_ix = 0
        self.global_symbols = GlobalSymbols(self)

    def _fp_vec_name(self, i, fld):
        return EncoderConfig.fp_vec_prefix + str(self.next_fp_vec_ix) + fld

    def get_fresh_fpvector(self):
        self.next_fp_vec_ix += 1
        return shared.FPVector(self.fp_sort, self._fp_vec_name(self.next_fp_vec_ix, ''), self.flds)

    def get_fresh_fp(self):
        self.next_fp_ix += 1
        if self.next_fp_ix == 1:
            ident = EncoderConfig.fresh_fp_prefix
        else:
            ident = EncoderConfig.fresh_fp_prefix + str(self.next_fp_ix)
        return self.fp_sort[ident]

    def get_fresh_reach_funs(self):
        self.next_r_ix += 1
        if self.next_r_ix == 1:
            fmt = EncoderConfig.reach_fun_prefix + '_{}'
        else:
            fmt = EncoderConfig.reach_fun_prefix + str(self.next_r_ix) + '_{}'

        return [z3.Function(fmt.format(k), self.sort.ref, self.sort.ref, z3.BoolSort())
                for k in range(1, self.n+1)]


    def global_constraint(self):
        if self.global_encoder_fn is not None:
            return self.global_encoder_fn(self)
        else:
            return c.BaseConstraint(symbols.Z3True,
                                    description = 'No global constraint')

    def encode_call(self, call, Y):
        assert isinstance(call, slast.PredCall), utils.wrong_type(call)
        assert isinstance(Y, shared.FPVector), utils.wrong_type(Y)
        if self.encode_call_fn is None:
            raise utils.SlothException('No call encoder specified')
        return self.encode_call_fn(self, call, Y)

class GlobalSymbols:
    """A container bundling the global variable names used in the encoding.

    Instantiated by and accessible through the configuration:

    >>> cnf = EncoderConfig({sl.list.struct : 2, sl.tree.struct : 1})
    >>> isinstance(cnf.global_symbols, GlobalSymbols)
    True

    """

    node_prefix = 'x'
    global_fp_prefix = 'X'

    def __init__(self, config):
        self.sort = config.sort
        self.fp_sort = config.fp_sort
        self.n = sum(config.bounds_by_struct.values())
        # TODO: Make 'X' into a constant (see also use below as well as in the conversion of models to graphs)
        self._X = shared.FPVector(self.fp_sort,
                                  GlobalSymbols.global_fp_prefix,
                                  config.flds)

    def x(self, i):
        """Get the i-th dedicated location variable"""
        return self.sort[(GlobalSymbols.node_prefix + '{}').format(i)]

    def xs(self):
        """
        >>> list(cnf.global_symbols.xs())
        [x0, x1, x2]
        """
        return (self.x(i) for i in range(self.n))

    def xs_set(self):
        """Return reference to a set that contains all `xs`.

        >>> cnf.global_symbols.xs_set() # doctest: +NORMALIZE_WHITESPACE
        Store(Store(Store(K(Int, False), x0, True), x1, True), x2, True) : SET(Int)
        """
        return lambdas.LambdaSet.to_set(self.sort,
                                        *(self.x(i) for i in range(self.n)))

    def X_vec(self):
        return self._X

    def X(self, fld = None):
        """Return the global FP variable for the given field.

        If no field is given, return the variable for the union.
        """
        suffix = fld if fld is not None else ''
        return self.fp_sort['X' + suffix]

    def Xs(self):
        yield self.X()
        flds = set()
        for s in self.all_structs:
            for f in s.fields:
                if f not in flds:
                    flds.add(f)
                    yield self.X(f)
