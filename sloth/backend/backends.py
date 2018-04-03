import z3

from .. import consts
from . import quantified, lambdas

class Backend:

    def __repr__(self):
        return self.description()

    def description(self):
        raise NotImplementedError("")

    def make_loc_sort(self, struct_name):
        raise NotImplementedError("")

class _QuantifiedBackend(Backend):

    def __init__(self):
        self.LocInterpretation = quantified.DeclaredSortLocInterpretation

    def description(self):
        return "Uninterpreted sorts & universal quantification"

    def make_loc_sort(self, struct_name):
        sort_name = consts.SL_PREFIX + struct_name + consts.LOC_SUFFIX
        return quantified.UninterpretedSort(sort_name)

class _LambdaBackend(Backend):

    def __init__(self):
        self.LocInterpretation = lambdas.IntegerLocInterpretation

    def description(self):
        return "Integer locations & lambdas"

    def make_loc_sort(self, struct_name):
        # Note: Important to make one instance per struct, because it tracks the constants of this sort!
        return lambdas.WrappedSort(z3.IntSort())

QuantifiedBackend = _QuantifiedBackend()
LambdaBackend = _LambdaBackend()

del _QuantifiedBackend
del _LambdaBackend

def exists(backend_str):
    return backend_str in registry

def get(backend_str):
    return registry[backend_str]

registry = {
    consts.QUANTIFIED_BACKEND : QuantifiedBackend,
    consts.LAMBDA_BACKEND : LambdaBackend
}
