import collections

import z3

from .. import consts, config
from ..encoder import encoder # TODO: Remove dependency on encoder
from ..utils import logger
from ..utils import utils
from . import model_utils

###############################################################################
# Single-Structure/Sort Model
###############################################################################

TypedLoc = collections.namedtuple('TypedLoc', 'loc struct')

def tag(struct):
    """Return a function for converting locations of the given structure into typed locations."""
    return lambda l : TypedLoc(l, str(struct))

class StructModel:
    """The interpretation of a single type of structure.

    Provides an interface to locations, constants etc. of the given
    structure in the given z3 model. :class:`model.SmtModel` is best
    viewed as a union of :class:`StructModel` instances for each type
    of predefined structure.

    """

    def __init__(self, struct, const_registry, z3_model, filter_sub_footprints = True, restrict_fns_to_footprints = True):
        self.filter_sub_footprints = filter_sub_footprints
        self.restrict_fns_to_footprints = restrict_fns_to_footprints
        self.struct = struct
        self.z3_model = z3_model
        self.locs = struct.LocInterpretation(struct, const_registry, z3_model)
        self.funcs = {}
        self._init_func_wrappers()
        fmt = 'Initialized {} model with locations {}, null node {}'
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
            funcs = ['  {} = {}'.format(fld, func) for fld, func in self.funcs.items()]

            fp_cs = self.fp_consts()
            if self.filter_sub_footprints:
                fp_cs = (c for c in fp_cs
                         if str(c).startswith(encoder.GlobalSymbols.global_fp_prefix))

            unsorted_fps = [(c,list(self.footprint(c))) for c in fp_cs]
            fps = sorted(unsorted_fps, key=lambda f : -len(f[1]))
            fp_strings = ['{}={}'.format(*f) for f in fps]
            fp_joined = ', '.join(list(fp_strings))
            fp_pretty = utils.lineify(fp_joined, split_at=', ', max_len=76)

            return (
                'Struct {} [\n'.format(self.struct.name) +
                '  locs = {}\n'.format(repr(self.locs)) +
                '  null = {}\n'.format(self.null()) +
                '\n'.join(funcs) + '\n' +
                '  footprints:\n' +
                utils.indented(fp_pretty) + '\n'
                ']'
            )
        else:
            return 'Struct {} [undefined]'.format(self.struct)

    def tagged_locs(self):
        return {tag(self.struct)(loc) : cs
                for loc, cs in self.locs.labeling.items()}

    def empty(self):
        return self.locs.empty()

    def null(self):
        return self.locs.null

    def loc_consts(self):
        return self.locs.consts

    def fp_consts(self):
        return self.locs.fp_consts

    def heap_fn(self, fld):
        return self.funcs[fld]

    def footprint(self, arr):
        return model_utils.eval_footprint(self.z3_model, self.locs, arr)

    def is_alloced(self, loc, fld):
        match = None
        for fp in self.locs.fp_consts:
            if str(fp) == encoder.GlobalSymbols.global_fp_prefix + fld:
                match = fp
                break
        assert match is not None, \
            "Couldn't check whether {} is allocated for {} in {}".format(loc, fld, self)
        return loc in self.footprint(match)

    def _init_func_wrappers(self):
        for fld in self.struct.fields:
            if self.restrict_fns_to_footprints:
                arr = self.struct.fp_sort[encoder.GlobalSymbols.global_fp_prefix + fld].ref
                locs = list(self.footprint(arr))
                logger.debug('Will init {}-func on locs {}'.format(fld, locs))
            else:
                locs = None

            self.funcs[fld] = model_utils.FuncWrapper(self.z3_model,
                                                      self.struct.heap_fn(fld),
                                                      locs)


###############################################################################
# Integrated Model
###############################################################################

class SmtModel:
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
        filter_aux_vars = not config.debug

        # If the global FP vars are defined, we limit function
        # interpretation to these footprints. This reflects the SL
        # partial function semantics: Field function should only be
        # defined on allocated nodes
        restrict_fns_to_footprints = self._defines_fps(z3_model, structs)

        logger.info('Constructing adapter for Z3 model')
        logger.debug('Model: {}'.format(z3_model))
        self.structs = structs
        self.struct_models = {
            s : StructModel(s, const_registry, z3_model,
                            filter_sub_footprints = filter_aux_vars,
                            restrict_fns_to_footprints = restrict_fns_to_footprints)
            for s in structs
        }
        # FIXME: This breaks for the lambda backend if we have multiple sorts
        self.node_labeling = utils.merge_dicts(
            *[self.struct_models[s].tagged_locs() for s in self.structs]
        )
        model_consts = list(model_utils.constants(z3_model))
        logger.debug('All constants in model: {}'.format(model_consts))
        logger.debug('Initialized SMT model with node labeling {}'.format(self.node_labeling))
        # TODO: Why does this crash without converting to strings?
        registered_consts = set(map(str, self.loc_consts() + self.fp_consts()))
        #registered_consts = set(self.loc_consts() + self.fp_consts())
        const_diff = (c for c in model_consts if str(c) not in registered_consts)
        non_lang_diff = (c for c in const_diff if not consts.SL_PREFIX in str(c))
        if filter_aux_vars:
            non_lang_diff = (c for c in non_lang_diff
                             if not str(c).startswith(consts.AUX_VAR_PREFIX))
        if non_lang_diff:
            fmt = ('Adapter contains constants {}, assuming the following'
                   + ' missing constants from the z3 model are data: {}')
            logger.debug(fmt.format(registered_consts, non_lang_diff))
            self.data = { c : model_utils.val_of(c, z3_model) for c in non_lang_diff }
        else:
            self.data = dict()

    def _defines_fps(self, z3_model, structs):
        try:
            sort = next(iter(structs)).fp_sort
        except:
            sort = None

        flds = utils.flatten(struct.fields for struct in structs)
        for fld in flds:
            fp_arr = sort[encoder.GlobalSymbols.global_fp_prefix + fld].ref
            #print('Checking {} --> {}'.format(fld, fp_arr))
            if z3_model.get_interp(fp_arr) is not None:
                return True
        else:
            #print('No FP defined')
            return False

    def __len__(self):
        """Total number of locations in all sorts combined."""
        return sum(len(self.struct_models[s]) for s in self.structs)

    def __iter__(self):
        """Iterate over the typed locations."""
        for typed_loc in self.typed_locs():
            yield typed_loc

    def __repr__(self):
        ordered_models = sorted(self.struct_models.items(),
                                key = lambda s : s[0].name)
        struct_strs = (str(s[1]) for s in ordered_models)
        lexicographic_data = sorted(self.data.items(), key=lambda i: str(i[0]))
        data_str = ', '.join(['{}={}'.format(*i) for i in lexicographic_data])
        if data_str:
            data_lines = ('Data [\n'
                          + utils.indented(
                              utils.lineify(data_str, split_at=', ', max_len = 76))
                          + '\n]'
                          )
        else:
            data_lines = 'Data [undefined]'
        joined = '\n'.join(struct_strs) + '\n' + data_lines
        return 'Model [\n' + utils.indented(joined) + '\n]'

    def struct_model(self, struct):
        """Return the interpretation of the given structure."""
        return self.struct_models[struct]

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
            return len(self.struct_models[struct])

    def locs(self, struct = None):
        """Generator for locations in the model.

        Yields either locations in a given structure or in the whole
        model if no struct argument is passed.

        """
        if struct is None:
            for m in self.struct_models.values():
                for loc in m:
                    yield loc
        else:
            for loc in self.struct_models[struct]:
                yield loc

    def typed_locs(self):
        """Generator for all typed locations in the model.

        Typed locations are tuples of locations together with
        references to the structure to which they belong. Including
        these references is necessary in the lambda backend, where
        locations are plain integers, so just looking at a location
        doesn't tell you to which structure it belongs.
        """
        for s, m in self.struct_models.items():
            for loc in m:
                yield tag(s)(loc)

    def null_node(self, struct):
        """Return the null node of the given struct."""
        return self.struct_models[struct].null()

    def loc_consts(self, struct = None):
        """Return list of all location consts in the given structure.

        If no structure is given, return list of all location
        constants in the entire model

        """
        if struct is None:
            return utils.flatten(self.struct_models[s].loc_consts() for s in self.structs)
        else:
            return self.struct_models[struct].loc_consts()

    def fp_consts(self, struct = None):
        """Return list of all footprint consts in the given structure.

        If no structure is given, return list of all footprint
        constants in the entire model

        """
        if struct is None:
            return utils.flatten(self.struct_models[s].fp_consts() for s in self.structs)
        else:
            return self.struct_models[struct].fp_consts()

    def heap_fn(self, struct, fld):
        """Return the interpretation of a heap function.

        Since a field of the same name may occur in several
        structures, both a structure and a field name must be passed
        to make the query unique.

        """
        assert(isinstance(fld, str))
        return self.struct_models[struct].heap_fn(fld)

    def footprint(self, struct, fp_const):
        """Return the interpretation of the given footprint constant.

        The struct for the footprint must be passed in, too, because
        depending on the backend, it is not clear in which structure
        interpretation the footprint must be looked up.

        """
        assert(fp_const.sort() == struct.fp_sort.ref)
        return self.struct_models[struct].footprint(fp_const)
