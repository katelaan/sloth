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
from . import backends
from . import symbols

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
        self.max_segs = config.max_num_stops(self)

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Struct({})".format(self.name)

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

###############################################################################
# Predefined structures
###############################################################################

def make_predef_structs(encoder_backend):
    """
    Instantiate a set of predefined structures with the given backend(s), which specify
    how to parse assertions about the structure and how to generate encodings of the structure.
    By default, we parse using the backend with uninterpreted sorts.
    """
    parser_backend = backends.QuantifiedBackend

    list_loc = parser_backend.make_loc_sort(consts.LIST_PRED)
    dlist_loc = parser_backend.make_loc_sort(consts.DLIST_PRED)
    tree_loc = parser_backend.make_loc_sort(consts.TREE_PRED)
    ptree_loc = parser_backend.make_loc_sort(consts.PTREE_PRED)

    list_enc_loc = encoder_backend.make_loc_sort(consts.LIST_PRED)
    dlist_enc_loc = encoder_backend.make_loc_sort(consts.DLIST_PRED)
    tree_enc_loc = encoder_backend.make_loc_sort(consts.TREE_PRED)
    ptree_enc_loc = encoder_backend.make_loc_sort(consts.PTREE_PRED)

    # TODO: Allocate data pointers in unrolling rules? -- See also FIXME in unrolling_rewriter in rewriting

    list_struct = Struct(consts.LIST_PRED,
                         input_sort_name = str(list_loc),
                         sort = list_enc_loc,
                         fields = {consts.FLD_NEXT : list_enc_loc.ref,
                                   consts.FLD_DATA : symbols.data_sort},
                         structural_fields = [consts.FLD_NEXT],
                         points_to_fields = [consts.FLD_NEXT],
                         unrolling_rules = [
                             Rule([Ptr(0, 1, consts.FLD_NEXT)])
                         ],
                         LocInterpretation = encoder_backend.LocInterpretation
    )
    dlist_struct = Struct(consts.DLIST_PRED,
                          input_sort_name = str(dlist_loc),
                          sort = dlist_enc_loc,
                          fields = {consts.FLD_NEXT : dlist_enc_loc.ref,
                                    consts.FLD_PREV : dlist_enc_loc.ref,
                                    consts.FLD_DATA : symbols.data_sort},
                          structural_fields = [consts.FLD_NEXT],
                          points_to_fields = [consts.FLD_NEXT, consts.FLD_PREV],
                          unrolling_rules = [
                              Rule([Ptr(0, 1, consts.FLD_NEXT), Ptr(1, 0, consts.FLD_PREV)]),
                              Rule([Ptr(0, 1, consts.FLD_NEXT)], force_null = [1])
                          ],
                          LocInterpretation = encoder_backend.LocInterpretation
    )
    tree_struct = Struct(consts.TREE_PRED,
                         input_sort_name = str(tree_loc),
                         sort = tree_enc_loc,
                         fields = {consts.FLD_LEFT : tree_enc_loc.ref,
                                   consts.FLD_RIGHT : tree_enc_loc.ref,
                                   consts.FLD_DATA : symbols.data_sort},
                         structural_fields = [consts.FLD_LEFT, consts.FLD_RIGHT],
                         points_to_fields = [consts.FLD_LEFT, consts.FLD_RIGHT],
                         unrolling_rules = [
                             Rule([Ptr(0, 1, consts.FLD_LEFT), Ptr(0, 2, consts.FLD_RIGHT)])
                         ],
                         LocInterpretation = encoder_backend.LocInterpretation
    )
    ptree_struct = Struct(consts.PTREE_PRED,
                          input_sort_name = str(ptree_loc),
                          sort = ptree_enc_loc,
                          fields = {consts.FLD_LEFT : ptree_enc_loc.ref,
                                    consts.FLD_RIGHT : ptree_enc_loc.ref,
                                    consts.FLD_PARENT : ptree_enc_loc.ref,
                                    consts.FLD_DATA : symbols.data_sort},
                          structural_fields = [consts.FLD_LEFT, consts.FLD_RIGHT],
                          points_to_fields = [consts.FLD_LEFT, consts.FLD_RIGHT, consts.FLD_PARENT],
                          unrolling_rules = [
                              # Both children non-null
                              Rule([Ptr(0, 1, consts.FLD_LEFT), Ptr(1, 0, consts.FLD_PARENT),
                                    Ptr(0, 2, consts.FLD_RIGHT), Ptr(2, 0, consts.FLD_PARENT)
                              ]),
                              # Left child non-null
                              Rule([Ptr(0, 1, consts.FLD_LEFT), Ptr(1, 0, consts.FLD_PARENT),
                                    Ptr(0, 2, consts.FLD_RIGHT)],
                                   force_null = [2]),
                              # Right child non-null
                              Rule([Ptr(0, 1, consts.FLD_LEFT),
                                    Ptr(0, 2, consts.FLD_RIGHT), Ptr(2, 0, consts.FLD_PARENT)],
                                   force_null = [1]),
                              # Both children null
                              Rule([Ptr(0, 1, consts.FLD_LEFT),
                                    Ptr(0, 2, consts.FLD_RIGHT)],
                                   force_null = [1,2])
                          ],
                          LocInterpretation = encoder_backend.LocInterpretation
    )

    return (list_struct, dlist_struct, tree_struct, ptree_struct)

###############################################################################
# Auxiliary functions for structures
###############################################################################

# def is_root_of_struct(structs, expr):
#     """Return true iff the given expression is a predicate (segment) call for one of the predefined structures."""
#     assert(isinstance(expr, z3.ExprRef))
#     for struct in structs:
#         if expr.decl() in struct.recursive_predicates():
#             logger.debug("{} is root of {}".format(expr, struct.name))
#             return True
#     return False

# def is_root_of(struct, expr):
#     assert(isinstance(struct, Struct))
#     assert(isinstance(expr, z3.ExprRef))
#     return expr.decl() in struct.parsable_decls()

def spatial_symbols(structs):
    """Returns a set of all defined spatial SL theory symbols.

    The set contains both the symbols for the given structures and the
    built-in symbols.

    """
    all_decls = [struct.spatial_decls() for struct in structs]
    return set(utils.flatten(all_decls) + [symbols.sep_con_fn, symbols.submodel_fn])

def print_struct_summary(struct):
    print("STRUCT {} [".format(struct))
    print("  location sort for input = {}".format(struct.input_sort_name))
    print("  location sort in encoding = {}".format(struct.sort))
    to_print = [z3utils.decl_to_string(decl) for decl in struct.parsable_decls()]
    for v in sorted(to_print):
        print("  " + v)
    print("]")

def print_sl_summary(structs):
    for s in structs:
        print_struct_summary(s)
