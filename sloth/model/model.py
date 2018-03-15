import collections

import z3

from .. import consts
from ..utils import logger
from ..utils import utils
from . import model_utils

###############################################################################
# Single-Structure/Sort Model
###############################################################################

TypedLoc = collections.namedtuple("TypedLoc", "loc struct")

def tag(struct):
    """Return a function for converting locations of the given structure into typed locations."""
    return lambda l : TypedLoc(l, str(struct))

class StructModel(object):
    """The interpretation of a single type of structure.

    Provides an interface to locations, constants etc. of the given
    structure in the given z3 model. :class:`model.SmtModel` is best
    viewed as a union of :class:`StructModel` instances for each type
    of predefined structure.

    """

    def __init__(self, struct, const_registry, z3_model):
        self.struct = struct
        self.z3_model = z3_model
        self.locs = struct.LocInterpretation(struct, const_registry, z3_model)
        self.funcs = {}
        self._init_func_wrappers()
        fmt = "Initialized {} model with locations {}, null node {}"
        logger.info(fmt.format(struct.predicate(), list(self.locs), self.null()))

    def __bool__(self):
        return bool(self.locs)

    def __len__(self):
        return len(self.locs)

    def __iter__(self):
        for l in self.locs:
            yield l

    def __repr__(self):
        if self:
            funcs = ["  {} = {}".format(fld, func) for fld, func in self.funcs.items()]
            if True: #False:
                unsorted_fps = [(c,list(self.footprint(c))) for c in self.fp_consts()]
                # TODO: CL option to include FPs in model
                # TODO: To figure out the FP mess, we might want to show empty ones as well
                #nonempty_fps = [(c,f) for (c,f) in unsorted_fps if f]
                #fps = sorted(nonempty_fps, key=lambda f : -len(f[1]))
                fps = sorted(unsorted_fps, key=lambda f : -len(f[1]))
                fp_strings = ["{}={}".format(*f) for f in fps]
                fp_joined = ", ".join(list(fp_strings))
                fp_pretty = utils.lineify(fp_joined, split_at=", ", max_len=76)

            return (
                "Struct {} [\n".format(self.struct.name) +
                "  locs = {}\n".format(repr(self.locs)) +
                "  null = {}\n".format(self.null()) +
                "\n".join(funcs) + "\n" +
                "  footprints:\n" +
                utils.indented(fp_pretty) + "\n"
                "]"
            )
        else:
            return "Struct {} [undefined]".format(self.struct)

    def tagged_locs(self):
        return {tag(self.struct)(loc) : cs
                for loc, cs in self.locs.labeling.items()}

    def empty(self):
        return self.locs.empty()

    def null(self):
        return self.locs.null

    def loc_consts(self):
        #print"RETURNING LOC CONSTS {}".format(list(self.locs.consts)))
        return self.locs.consts

    def fp_consts(self):
        #print"RETURNING FP CONSTS {}".format(list(self.locs.fp_consts)))
        return self.locs.fp_consts

    def heap_fn(self, fld):
        return self.funcs[fld]

    def footprint(self, arr):
        assert(isinstance(arr, z3.ArrayRef))
        if model_utils.val_of(arr, self.z3_model) is not None:
            # TODO: More efficient way to evaluate array?
            for loc in self:
                #print("{} evals to {}".format(loc,self.z3_model.eval(arr[loc])))
                if self.z3_model.eval(arr[loc]):
                    yield loc

    def _init_func_wrappers(self):
        self.funcs = { fld : model_utils.FuncWrapper(self.z3_model, self.struct.heap_fn(fld))
                       for fld in self.struct.fields }


###############################################################################
# Integrated Model
###############################################################################

class SmtModel(object):
    """An adapter for :class:`z3.ModelRef` models.

    Based on a set of predefined structures as well as a
    :class:`backend.generic.ConstRegistry`, this class provides a
    nicer API for accessing the interpretations of sorts, constants,
    functions, etc. as well as a more readable string representation.

    For use both in pretty-printing and in further processing,
    e.g. plotting.

    """

    def __init__(self, z3_model, const_registry, structs):
        self.z3_model = z3_model
        logger.info("Constructing adapter for Z3 model")
        logger.debug("Model: {}".format(z3_model))
        self.structs = structs
        self._struct_models = { s : StructModel(s, const_registry, z3_model) for s in structs}
        # FIXME: This breaks for the lambda backend if we have multiple sorts
        self.node_labeling = utils.merge_dicts(
        *[self._struct_models[s].tagged_locs() for s in self.structs]
        )
        model_consts = list(model_utils.constants(z3_model))
        logger.debug("All constants in model: {}".format(model_consts))
        logger.debug("Initialized SMT model with node labeling {}".format(self.node_labeling))
        registered_consts = set(map(str, self.loc_consts() + self.fp_consts()))
        #registered_consts = set(self.loc_consts() + self.fp_consts())
        # TODO: WHy does this crash without going through strings?
        const_diff = [c for c in model_consts if str(c) not in registered_consts]
        non_lang_diff = [c for c in const_diff if not consts.SL_PREFIX in str(c)]
        if non_lang_diff:
            fmt = ("Adapter contains constants {}, assuming the following"
                   + " missing constants from the z3 model are data: {}")
            logger.debug(fmt.format(registered_consts, non_lang_diff))
            self.data = { c : model_utils.val_of(c, z3_model) for c in non_lang_diff }
        else:
            self.data = dict()

    def __len__(self):
        """Total number of locations in all sorts combined."""
        return sum(len(self._struct_models[s]) for s in self.structs)

    def __iter__(self):
        """Iterate over the typed locations."""
        for typed_loc in self.typed_locs():
            yield typed_loc

    def __repr__(self):
        ordered_models = sorted(self._struct_models.items(),
                                key = lambda s : s[0].name)
        struct_strs = (str(s[1]) for s in ordered_models)
        data_str = ", ".join(["{}={}".format(*i) for i in self.data.items()])
        if data_str:
            data_lines = ("Data [\n"
                          + utils.indented(
                              utils.lineify(data_str, split_at=", ", max_len = 76))
                          + "\n]"
                          )
        else:
            data_lines = "Data [undefined]"
        joined = "\n".join(struct_strs) + "\n" + data_lines
        return "Model [\n" + utils.indented(joined) + "\n]"

    def struct_model(self, struct):
        """Return the interpretation of the given structure."""
        return self._struct_models[struct]

    def val_of(self, const):
        """Return the value of the given constant in the model."""
        # TODO: This is the only function of this class which goes into the model directly. Maybe delegate this to the structure interpretations as well?
        return model_utils.val_of(const, self.z3_model)

    def num_locs(self, struct = None):
        """Return the number of locations in the given struct.

        If no struct is passed in, behaves like len()."""
        if struct is None:
            return len(self)
        else:
            return len(self._struct_models[struct])

    def locs(self, struct = None):
        """Generator for locations in the model.

        Yields either locations in a given structure or in the whole
        model if no struct argument is passed.

        """
        if struct is None:
            for m in self._struct_models.values():
                for loc in m:
                    yield loc
        else:
            for loc in self._struct_models[struct]:
                yield loc

    def typed_locs(self):
        """Generator for all typed locations in the model.

        Typed locations are tuples of locations together with
        references to the structure to which they belong. Including
        these references is necessary in the lambda backend, where
        locations are plain integers, so just looking at a location
        doesn't tell you to which structure they belong.
        """
        for s, m in self._struct_models.items():
            for loc in m:
                yield tag(s)(loc)

    def null_node(self, struct):
        """Return the null node of the given struct."""
        return self._struct_models[struct].null()

    def loc_consts(self, struct = None):
        """Return list of all location consts in the given structure.

        If no structure is given, return list of all location
        constants in the entire model

        """
        if struct is None:
            return utils.flatten(self._struct_models[s].loc_consts() for s in self.structs)
        else:
            return self._struct_models[struct].loc_consts()

    def fp_consts(self, struct = None):
        """Return list of all footptins consts in the given structure.

        If no structure is given, return list of all footprint
        constants in the entire model

        """
        if struct is None:
            return utils.flatten(self._struct_models[s].fp_consts() for s in self.structs)
        else:
            return self._struct_models[struct].fp_consts()

    def heap_fn(self, struct, fld):
        """Return the interpretation of a heap function.

        Since a field of the same name may occur in several
        structures, both a structure and a field name must be passed
        to make the query unique.

        """
        assert(isinstance(fld, str))
        return self._struct_models[struct].heap_fn(fld)

    def footprint(self, struct, fp_const):
        """Return the interpretation of the given footprint constant.

        The struct for the footprint must be passed in, too, because
        depending on the backend, it is not clear in which structure
        interpretation the footprint must be looked up.

        """
        assert(fp_const.sort() == struct.fp_sort.ref)
        return self._struct_models[struct].footprint(fp_const)
