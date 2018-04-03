import z3

from ..utils import logger
from ..model import model_utils
from . import generic, symbols

class WrappedSort(generic.SlSort):
    def __init__(self, z3_sort):
        assert(isinstance(z3_sort, z3.SortRef))
        super().__init__(z3_sort, LambdaSet)

    def __str__(self):
        return str(self.ref)

    def to_declare(self):
        # Wrapping built-in sort => Should not result in sort decl
        return False


class LambdaSet(generic.Set):
    def __init__(self, ref, elem_sort):
        logger.debug("Creating new lambda set from {}".format(ref))
        super().__init__(ref, elem_sort)

    @staticmethod
    def get_empty(elem_sort):
        return LambdaSet(z3.K(elem_sort.ref, False), elem_sort)

    def _empty(self):
        return LambdaSet.get_empty(self.elem_sort)

    def is_empty(self):
        return self.ref == self._empty().ref

    def non_empty(self):
        return z3.Not(self.ref == self._empty().ref)

    def insert(self, elem):
        return LambdaSet(z3.Store(self.ref, elem, True), self.elem_sort)

    def remove(self, elem):
        return LambdaSet(z3.Store(self.ref, elem, False), self.elem_sort)

    def is_singleton(self, elem):
        return self.ref == self._empty().insert(elem).ref

    def contains(self, elem):
        return z3.Select(self.ref, elem)

    def subset_of(self, other):
        return other.ref == z3.Map(symbols.or_decl, self.ref, other.ref)

    def disjoint_from(self, other):
        return self._empty().ref == z3.Map(symbols.and_decl, self.ref, other.ref)

    def is_identical(self, other):
        return self.ref == other.ref

    def union_of(self, part1, part2):
        return self.ref == z3.Map(symbols.or_decl, part1.ref, part2.ref)

    def union_without_elem(self, part1, part2, elem):
        return z3.And(self.contains(elem),
                      self.remove(elem).union_of(part1, part2))


class IntegerLocInterpretation(generic.LocInterpretation):
    def __init__(self, struct, const_registry, z3_model):
        super().__init__(struct, const_registry, z3_model)
        if self._is_used():
            self._gather_locs()
        self._init_node_labeling()

    def __repr__(self):
        return "Integers("+super().__repr__()+")"

    def _gather_locs(self):
        acc = set(map(lambda c : model_utils.val_of(c, self.z3_model), self.consts))
        for fld in self.struct.fields:
            if not self.struct.is_data_field(fld):
                fn = self.struct.heap_fn(fld)
                wrapper = model_utils.FuncWrapper(self.z3_model, fn)
                logger.debug("Values for {}: {}".format(fn, wrapper.all_vals()))
                acc |= wrapper.all_vals()
        self._locs = acc
