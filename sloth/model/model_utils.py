###############################################################################
# Processing Z3 models
###############################################################################

import z3

from ..utils import utils
from ..utils import logger

# TODO: Currently this function is invoked fairly frequently. (Even though constants are actually already known at parse time.) Either remove this function or memoize?
def constants(z3_model):
    """Return all externally defined (rather than z3's internally defined) constants in the model"""
    external = lambda d : '!' not in repr(d)
    for d in z3_model.decls():
        if external(d):
            yield d

def val_of(const, z3_model):
    try:
        return z3_model[const]
    except z3.Z3Exception as e:
        fmt = 'Trying to look up value of {} of type {} in z3 model'
        logger.info('Caught exception {}'.format(e))
        raise utils.IllegalSolverState(fmt.format(const, const.__class__)) from None

def eval_footprint(z3_model, locs, arr):
    assert isinstance(arr, z3.ArrayRef), utils.wrong_type(arr)
    # TODO: More efficient way to evaluate array?
    if val_of(arr, z3_model) is not None:
        for loc in locs:
            if z3_model.eval(arr[loc]):
                yield loc

class FuncWrapper:

    def __init__(self, z3_model, fn, locs = None):
        assert(isinstance(fn, z3.FuncDeclRef))
        if locs is None:
            self.default_init(z3_model, fn)
        else:
            self.init_on_locs(z3_model, fn, locs)

    def default_init(self, z3_model, fn):
        as_list = z3_model[fn].as_list() if z3_model[fn] else []
        if not as_list:
            self.else_val = None
            self.defined_vals = {}
        else:
            self.else_val = as_list[-1]
            pairs = as_list[:-1]
            self.defined_vals = dict(pairs)

    def init_on_locs(self, z3_model, fn, locs):
        as_list = z3_model[fn].as_list() if z3_model[fn] else []
        if as_list:
            # TODO: Reduce code duplication with other init function
            pairs = [(loc, z3_model.eval(fn(loc))) for loc in locs]
            #print('Func vals: {}'.format(pairs))
            self.defined_vals = dict(pairs)
            self.else_val = as_list[-1]
        else:
            self.else_val = None
            self.defined_vals = {}

    def __call__(self, loc):
        if loc in self.defined_vals:
            return self.defined_vals[loc]
        else:
            if not self.is_defined():
                print('Warning: Trying to evaluate completely undefined function.')
            return self.else_val

    def __repr__(self):
        if self.is_defined():
            defined = ['{}->{}'.format(k,self(k))
                       for k in sorted(self.defined_vals, key=lambda v: int(str(v)))]
            if self.else_val is not None:
                default = ', else->{}'.format(self.else_val)
            else:
                default = ''
            return ', '.join(defined) + default
        else:
            return 'undefined'

    def is_defined(self):
        return self.else_val is not None or self.defined_vals

    def default_val(self):
        return self.else_val

    def all_vals(self):
        acc = set()
        if self.is_defined():
            for k in self.defined_vals:
                acc.add(k)
                acc.add(self.defined_vals[k])
            acc.add(self.else_val)
        return acc
