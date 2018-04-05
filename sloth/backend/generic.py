import z3

from ..utils import logger, utils
from ..model import model_utils
from . import symbols, struct

def const(name, sort):
    assert(isinstance(name, str))
    return z3.Const(name, sort)

def array(name, ix_sort, cont_sort):
    return z3.Array(name, ix_sort, cont_sort)

class SlSort:
    """Representation of a separation logic sort.

    Depending on the backend, this could be either an uninterpreted sort or a
    built-in sort (Int).

    Indexing into the sort object with a string returns a constant of
    the sort of the given name.
    """

    def __init__(self, ref, set_class):
        """
        Create new separation logic sort whose elements are of sort `ref` in Z3.

        :param: ref: Reference type to be used for elements of this sort in z3 (of type :class:`z3.SortRef`)
        :param: set_class: Subclass of Set used to create sets of this sort.
        """
        assert(isinstance(ref, z3.SortRef))
        self.ref = ref
        self.set_class = set_class

    def to_declare(self):
        """Must this sort be declared in the SMT2 encoding?"""
        raise NotImplementedError("Not specified whether sort must be declared")

    def set_sort(self):
        """Return the set / footprint sort associated with this sort."""
        return SetSort(self.set_class, self)

    def __getitem__(self, elem):
        """Return a constant of this sort of the given string name."""
        return const(elem, self.ref)

class Set:
    """Representation of a set of locations / footprint."""

    def __init__(self, ref, elem_sort):
        """Create a new set"""
        self.ref = ref
        self.elem_sort = elem_sort

    def __repr__(self):
        return "{} : SET({})".format(self.ref, self.elem_sort)

    @staticmethod
    def get_empty(elem_sort):
        """Return encoding of an empty set"""
        raise NotImplementedError("")

    def is_empty(self):
        """Return constraint expressing that this set is empty"""
        raise NotImplementedError("")

    def non_empty(self):
        """Return constraint expressing that this set is nonempty"""
        raise NotImplementedError("")

    def insert(self, elem):
        """Return a new set that additionally contains `elem`"""
        raise NotImplementedError("")

    def remove(self, elem):
        """Return a new set with `elem` removed"""
        raise NotImplementedError("")

    def is_singleton(self, elem):
        """Return constraint expressing that `self` is the singleton set containing `elem`"""
        raise NotImplementedError("")

    def contains(self, elem):
        """Return constraint expressing that this set contains the given element"""
        raise NotImplementedError("")

    def subset_of(self, other):
        """Return constraint expressing that `self` is a subset of `other`"""
        raise NotImplementedError("")

    def disjoint_from(self, other):
        """Return constraint expressing that `self` is disjoint from `other`"""
        raise NotImplementedError("")

    def is_identical(self, other):
        """Return constraint expressing that `self` is identical to `other`"""
        raise NotImplementedError("")

    def union_of(self, part1, part2):
        """Return constraint expressing that `self` is the union of `part1` and `part2`"""
        raise NotImplementedError("")

    def union_of_all(self, *parts):
        """Return constraint expressing that `self` is the union of all `parts`"""
        raise NotImplementedError("")

    def union_without_elem(self, part1, part2, elem):
        """Return constraint expressing that after removing `elem` from `self`,
        the result is the union of `part1` and `part2`"""
        raise NotImplementedError("")


class SetSort:
    """A separation logic set / footprint sort associated with a
    :class:`backend.generic.SlSort`

    Indexing into the sort object with a string returns a constant of
    the set sort of the given name.
    """

    def __init__(self, set_class, elem_sort):
        assert(isinstance(elem_sort, SlSort))
        self.set_class = set_class
        self.elem_sort = elem_sort
        self.ref = z3.ArraySort(self.elem_sort.ref, z3.BoolSort())
        self.consts = set()

    def __getitem__(self, name):
        """Return a constant of this sort of the given string name."""
        assert(isinstance(name, str))
        set_ref = array(name, self.elem_sort.ref, z3.BoolSort())
        return self.set_class(set_ref, self.elem_sort)

class LocInterpretation:
    """Interpretation of a location sort in a z3 model.

    Represents the interpretation of the location sort itself as well
    as all (plain and footprint) constants of a
    :class:`sloth.backend.struct.Struct` in a :class:`z3.ModelRef`.

    The set of constants is restricted to constants that are both

    1. known to the :class:`backend.generic.ConstRegistry` passed to
       the constructor
    2. interpreted by the z3 model (not None in the z3 model)

    This makes `LocInterpretation` a safe interface for iterating over
    constants, since neither redundant/unused constants in the
    encoding (which may not occur in the z3 model) nor internal
    constants introduced by z3 (which are in the z3 model but not part
    of our encoding) are contained in the `const` and `fp_consts`
    attributes.

    """

    def __init__(self, struct, const_registry, z3_model):
        self.struct = struct
        self.z3_model = z3_model
        self._locs = []
        self.labeling = {}

        # Initialize constants based on the registry & the model
        self.consts = list(const_registry.defined_locs(struct, z3_model))
        #print("CONSTS IN LOC INTERPRETATION: {}".format(self.consts))
        if self.consts:
            self.null = model_utils.val_of(struct.null, z3_model)
        else:
            self.null = None
        self.fp_consts = list(const_registry.defined_fps(struct, z3_model))

        # TODO: Locs must currently be initialized in the subclass after calling super and before calling _init_node_labeling --> Make less error prone

    def _is_used(self):
        # TODO: The following isn't true any more, is it?
        # The null constant is always there, because it is declared for the parser
        # Thus we define that a sort is used if it contains at least one more const
        #null_set = set([self.struct.null])
        #return self.struct.sort.consts != null_set
        return bool(self.consts)

    def __bool__(self):
        return bool(self._locs)

    def __iter__(self):
        for l in self._locs:
            yield l

    def __len__(self):
        return len(self._locs)

    def __repr__(self):
        def node_repr(k,v):
            if v:
                return "{}:{}".format(k,v)
            else:
                return str(k)
        return ", ".join(map(lambda i : node_repr(*i),self.labeling.items()))

    def empty(self):
        """Is this sort interpreted by an empty set of locations (or not at all)?"""
        return not bool(self)

    def _init_node_labeling(self):
        if not self._is_used():
            return

        labeling = dict([(loc,[]) for loc in self._locs])
        for c in self.consts:
            try:
                loc = model_utils.val_of(c, self.z3_model)
                labeling[loc].append(c)
            except KeyError as e:
                if loc is None:
                    fmt = "Adding {} to labeling of {} failed --> {} not actually used in model"
                    logger.debug(fmt.format(c, loc, c))
                else:
                    fmt = ("Inconsistent internal state: location {} interprets {}"
                           + "in z3 model, but model adapter contains only locs {}")
                    raise utils.IllegalSolverState(fmt.format(loc,c,self._locs))
        self.labeling = labeling


class ConstRegistry:
    """Cache for keeping track of constants introduced in an encoding.

    Use case: Add all constants that appear in an encoding to a
    :class:`ConstRegistry` and pass that registry to all
    :class:`LocInterpretation` instances you create. This guarantees
    that the set of constants accessible through the intepretation is
    the intersection of the constants in the encoding and the
    :class:`z3.ModelRef` model returned by z3.

    """

    LOC = False
    FP = True
    DATA = "data"

    def __init__(self, structs):
        self.structs = structs
        self._cache = {(struct, typ) : set()
                       for struct in structs
                       for typ in [self.LOC, self.FP]}
        self._cache.update({(self.DATA,self.LOC) : set()})

    def __repr__(self):
        lines = []
        for (s,t), cs in self._cache.items():
            if cs:
                typ = "locs" if t == self.LOC else "foots"
                lines.append("{}-{} = {}".format(s, typ, cs))
        return "consts(\n" + utils.indented("\n".join(lines)) + "\n)"

    def add_const(self, struct, const):
        """Add the given const to the cache for the given struct."""
        #print("REGISTRY: {}".format(const))
        if const.sort() == struct.fp_sort.ref:
            self._cache[(struct, self.FP)].add(const)
        elif const.sort() == struct.sort.ref:
            self._cache[(struct, self.LOC)].add(const)
        else:
            fmt = "Constant of wrong sort {} added to {} registry"
            raise utils.IllegalSolverState(fmt.format(const.__class__, struct))

    def add_data_const(self, const):
        assert(const.sort() == symbols.data_sort)
        self._cache[(self.DATA, self.LOC)].add(const)

    # TODO: Memoize?
    def _defined_consts(self, key, z3_model):
        try:
            for c in self._cache[key]:
                if model_utils.val_of(c, z3_model) is not None:
                    yield c
        except KeyError:
            fmt = "Registry not defined for {} of {}"
            typ = "locations" if key[1] == self.LOC else "footprints"
            raise utils.IllegalSolverState(fmt.format(typ, key[0]))

    def has_consts(self, struct):
        """Does this registry contain any (location) consts of the given struct?"""
        return bool(self._cache[(struct, self.LOC)])

    def defined_locs(self, struct, z3_model):
        """Generator for location consts of given struct in given model.

        No order on the returned consts guaranteed."""
        return self._defined_consts((struct, self.LOC), z3_model)

    def defined_data(self, z3_model):
        return self._defined_consts((self.DATA, self.LOC), z3_model)

    def defined_fps(self, struct, z3_model):
        """Generator for footprint consts of given struct in given model.

        No order on the returned consts guaranteed."""
        return self._defined_consts((struct, self.FP), z3_model)
