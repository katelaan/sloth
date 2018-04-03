"""Definition of recursive data structures.

Throughout the lifetime of the solver, from parsing all the way to
plotting, a list of :class:`sloth.backend.Struct` objects defines
which data structures can be used, how they can be described (i.e.,
the associated theory symbols) and what their semantics are (via
:class:`sloth.backend.Rule` instances).

"""

import collections

import z3

from .. import consts, config
from ..utils import utils
# FIXME: Disentangle the cyclic dependencies between the backend modules...
#from . import generic. (See commented lines with generic reference here)

class StructureAccessException(utils.SlothException):
    """Thrown upon attempted access of undefined function declarations or fields"""

Ptr = collections.namedtuple("Ptr", ["src", "trg", "fld"])

class Rule:
    """A rule defining one option to unfold a recursive structure."""
    def __init__(self, ptrs, force_null = []):
        for ptr in ptrs:
            assert(isinstance(ptr, Ptr))
        self.ptrs = ptrs
        self.non_null = [ptr.src for ptr in ptrs]

class Struct:
    """Representation of a recursively defined data structure."""

    # TODO: Memoize some of the definitions? Especially all those that collect declarations!

    def __init__(self, name, input_sort_name, sort,
                 fields = {}, structural_fields = [], points_to_fields = [],
                 unrolling_rules = [],
                 LocInterpretation = object): # = generic.LocInterpretation):
        assert(isinstance(name, str))
        assert(isinstance(input_sort_name, str))
        #assert(isinstance(sort, generic.SlSort))
        assert(len(fields) > 0)
        assert(len(points_to_fields) > 0)
        self.unqualified_name = name
        self.name = consts.SL_PREFIX + name
        self.input_sort_name = input_sort_name
        self.sort = sort
        self.fields = fields
        self.structural_fields = structural_fields
        self.points_to_fields = points_to_fields
        self.unrolling_rules = unrolling_rules
        self.LocInterpretation = LocInterpretation

        # Derived attributes
        # The footprint sort associated with the struct.
        self.fp_sort = self.sort.set_sort()
        self.null = self.sort[self.name + consts.NULL_SUFFIX]

        self.branching_factor = len(structural_fields)
        assert(self.branching_factor >= 1)
        #self._check_rule_order()

        data_fields = set(self.fields.keys()).difference(self.points_to_fields)
        # Currently, we only propertly support one data field per structure!
        assert(len(data_fields) == 1)
        self.data_field = list(data_fields)[0]

        self.decl_mapping = None
        self._init_decl_mapping()
        self.max_segs = config.max_num_stops(self)

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Struct({})".format(self.name)

    def _init_decl_mapping(self):
        # TODO: Get rid of cyclic dependency between struct and symbols
        from . import symbols

        self._decl_mapping = {
        symbols.sep_con_fn : z3.Function(self.name+"."+consts.SEP_CON_SUFFIX,
                                 z3.BoolSort(), z3.BoolSort(), z3.BoolSort()),
        symbols.submodel_fn : z3.Function(self.name+"."+consts.SUBMODEL_SUFFIX,
                                  z3.BoolSort(), z3.BoolSort()),
        symbols.and_decl : z3.Function(self.name+"."+consts.CONJUNCTION_SUFFIX,
                                               z3.BoolSort(), z3.BoolSort(), z3.BoolSort()),
        symbols.or_decl : z3.Function(self.name+"."+consts.DISJUNCTION_SUFFIX,
                                               z3.BoolSort(), z3.BoolSort(), z3.BoolSort()),
        symbols.not_decl : z3.Function(self.name+"."+consts.NEGATION_SUFFIX,
                                               z3.BoolSort(), z3.BoolSort())
    }

    def _check_rule_order(self):
        for rule in self.unrolling_rules:
            for ptr in enumerate(rule.ptrs):
                if (ptr.src == 0):
                    # FIXME: Currently order of structural fields has to match order of pointers in rule declaration due to brittle construction of rule constraints in unrolling. Should revisit this after we have generic backends and/or handle data constraints
                    logger.debug("{} {}".format(self.points_to_fields[ptr.trg], ptr.fld))
                    assert(self.points_to_fields[ptr.trg] == ptr.fld)

    ##############################
    # Parsing
    ##############################

    def predicate(self):
        """The predicate declaration for asserting this structure in SMTLIB2"""
        return z3.Function(self.name, self.sort.ref, z3.BoolSort())

    def segment_predicate(self, num_stops):
        """Predicate declaration for asserting a structure segment with the given number of stop points"""
        assert(num_stops >= 1)
        assert((not self.is_linear()) or num_stops == 1)
        sorts = ([self.sort.ref] * (num_stops+1)) + [z3.BoolSort()]
        return z3.Function(consts.seg_decl_name(self, num_stops), *sorts)

    def unary_data_predicate(self, num_stops):
        assert(num_stops >= 0)
        assert((not self.is_linear()) or num_stops <= 1)
        # First argument is the data predicate, the others are root + stop nodes
        sorts = [z3.BoolSort()] + [self.sort.ref] * (num_stops+1) + [z3.BoolSort()]
        return z3.Function(consts.data_decl_name(self, None, num_stops), *sorts)

    def data_predicate(self, fld, num_stops):
        assert(num_stops >= 0)
        assert((not self.is_linear()) or num_stops <= 1)
        # First argument is the data predicate, the others are root + stop nodes
        sorts = [z3.BoolSort()] + [self.sort.ref] * (num_stops+1) + [z3.BoolSort()]
        return z3.Function(consts.data_decl_name(self, fld, num_stops), *sorts)

    def points_to_predicate(self):
        """Returns predicate for allocating all structural fields at the same time."""
        sorts = ([self.sort.ref]
                 + [self.fields[k] for k in self.points_to_fields]
                 + [z3.BoolSort()])
        return z3.Function(self.name+consts.POINTS_TO_SUFFIX, *sorts)

    def fld_predicate(self, fld):
        """Returns predicate for single-field assertions, x ->_{fld} y."""
        assert(isinstance(fld, str))
        assert(fld in self.fields)
        return z3.Function(self.name + "." + fld,
                           self.sort.ref, self.fields[fld], z3.BoolSort())

    def equality_predicate(self):
        sorts = [self.sort.ref, self.sort.ref, z3.BoolSort()]
        return z3.Function(self.name + consts.EQ_SUFFIX, *sorts)

    def disequality_predicate(self):
        sorts = [self.sort.ref, self.sort.ref, z3.BoolSort()]
        return z3.Function(self.name + consts.NEQ_SUFFIX, *sorts)

    ###############################################################################
    # Utilities for getting all symbols of a certain type
    ###############################################################################

    def spatial_decls(self):
        return ([self.points_to_predicate(),self.equality_predicate(),self.disequality_predicate()]
                + [self.fld_predicate(fld) for fld in self.fields]
                + self.recursive_predicates()
                + self.data_predicates())

    def data_predicates(self):
        return ([self.data_predicate(fld, i)
                for fld in self.fields
                for i in range(self.max_segs+1)]
                + [self.unary_data_predicate(i)
                   for i in range(self.max_segs+1)])

    def parsable_decls(self):
        """Return all SMTLIB2 function decls associated with this struct.
        Optionally, the max. number of stop constraints can be set by the second parameter."""
        return (self.spatial_decls() + [self.null])

    def recursive_predicates(self):
        """Return all SMTLIB2 function decls associated with non-data recursive calls.

        (As opposed to individual pointers.)"""
        return ([self.predicate()]
                + [self.segment_predicate(i+1) for i in range(self.max_segs)])

    def decl_map(self):
        """Return dictionary of all parsable declarations associated with this struct.
        Optionally, the max. number of stop constraints can be set by the second parameter."""
        return { str(f) : f for f in self.parsable_decls() }

    ##############################
    # Encoding
    ##############################

    def sorted_version(self, pred):
        """Return a tagged variant of the given predicate symbol
        (for use in typing the SMT input)"""
        try:
            return self._decl_mapping[pred]
        except KeyError:
            raise StructureAccessException("No sorted version of {}".format(pred))

    def sorted_versions(self):
        return self._decl_mapping.values()

    def heap_fns(self):
        """Return generator for all heap functions associated with this structure,
        i.e., all those functions that occur as uninterpreted sorts in the SMT encoding."""
        for fld in self.fields:
            yield self.heap_fn(fld)

    def heap_fn(self, fld):
        """Get function declaration for the field's (unary) heap function in the model."""
        assert(isinstance(fld, str))
        if fld in self.fields:
            return z3.Function(self.name + "." + fld, self.sort.ref, self.fields[fld])
        else:
            fmt = "Attempting to access function for undefined fld {} of structure {}"
            raise StructureAccessException(fmt.format(fld, self))

    ##############################
    # Utilities
    ##############################

    def is_data_field(self, fld):
        assert(fld in self.fields)
        return fld not in self.points_to_fields

    def is_linear(self):
        """Does this structure have just one success of its own sort?"""
        return self.branching_factor == 1
