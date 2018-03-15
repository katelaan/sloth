import z3

from ..utils import logger
from ..z3api import z3utils
from . import generic

class UninterpretedSort(generic.SlSort):
    def __init__(self, name):
        assert(isinstance(name, str))
        super(UninterpretedSort, self).__init__(z3.DeclareSort(name), QuantifiedSet)

    def __str__(self):
        return str(self.ref)

    def __repr__(self):
        return "LS(" + repr(self.ref) + ")"

    def to_declare(self):
        # New uninterpreted sort => Must result in sort decl
        return True

    def domain_is(self, elems):
        x = z3.Const("x", self.ref)
        return z3.ForAll(x, z3.Or([x == n for n in elems]))


class QuantifiedSet(generic.Set):
    def __init__(self, ref, elem_sort):
        logger.debug("Creating new quantified set from {}".format(ref))
        super(QuantifiedSet, self).__init__(ref, elem_sort)

    def is_empty(self):
        x = generic.const("_x_", self.elem_sort.ref)
        return z3.ForAll(x, z3.Not(self.contains(x)))

    def non_empty(self):
        x = generic.const("_x_", self.elem_sort.ref)
        return z3.Exists(x, self.contains(x))

    def insert(self, elem):
        return QuantifiedSet(z3.Store(self.ref, elem, True), self.elem_sort)

    def remove(self, elem):
        return QuantifiedSet(z3.Store(self.ref, elem, False), self.elem_sort)

    def is_singleton(self, elem):
        #print(self.remove(elem))
        #print(self.remove(elem).is_empty())
        return z3.And(self.contains(elem), self.remove(elem).is_empty())

    def contains(self, elem):
        assert(self.elem_sort.ref == elem.sort())
        return z3.Select(self.ref, elem)

    def subset_of(self, other):
        x = generic.const("_x_", self.elem_sort.ref)
        return z3.ForAll(x, z3.Or(z3.Not(self.contains(x)), other.contains(x)))

    def disjoint_from(self, other):
        x = generic.const("_x_", self.elem_sort.ref)
        return z3.ForAll(x, z3.Not(z3.And(self.contains(x), other.contains(x))))

    def is_identical(self, other):
       x = generic.const("_x_", self.elem_sort.ref)
       return z3.ForAll(x, self.contains(x) == other.contains(x))

    def union_of(self, part1, part2):
        x = generic.const("_x_", self.elem_sort.ref)
        return z3.ForAll(x, z3.Or(part1.contains(x), part2.contains(x)) == self.contains(x))

    def union_without_elem(self, part1, part2, elem):
        x = generic.const("_x_", self.elem_sort.ref)
        return z3.ForAll(x, z3.Or(part1.contains(x), part2.contains(x)) == self.remove(elem).contains(x))


class DeclaredSortLocInterpretation(generic.LocInterpretation):

    def __init__(self, struct, const_registry, z3_model):
        super(DeclaredSortLocInterpretation, self).__init__(struct, const_registry, z3_model)
        universe = z3_model.get_universe(struct.sort.ref)
        if universe is not None:
            logger.info("Universe for {} is {}".format(struct.sort.ref, universe))
            self._locs = list(universe)
        self._init_node_labeling()

    def __repr__(self):
        return "SortInterpretation("+super(DeclaredSortLocInterpretation, self).__repr__()+")"
