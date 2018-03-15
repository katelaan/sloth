from z3 import And, Or, Not, ExprRef, is_const, ArithRef

from ..utils import logger, utils
from .exceptions import debug_encoding_enabled
from ..backend import generic, struct as struct_mod
from ..backend.symbols import LAnd
from .footprints import to_fp_dict

class SplitEncoding(object):
    def __init__(self, structure, footprint):
        self.structure = structure
        self.footprint = footprint

    def merged(self):
        fs = [f for f in (self.structure, self.footprint) if f is not None]
        return LAnd(fs)

    def negate(self):
        # Footprint remains positive!
        self.structure = Not(self.structure)

    def __repr__(self):
        return "SplitEncoding(structure = {!r}, footprint = {!r})".format(self.structure, self.footprint)

def fld_points_to(struct, fld, src, trg, foot):
    if debug_encoding_enabled:
        assert(isinstance(fld, str))
        assert(isinstance(src, ExprRef))
        assert(isinstance(trg, ExprRef))
        assert(isinstance(foot, generic.Set))

    return SplitEncoding(
        structure = And(trg == struct.heap_fn(fld)(src), Not(src == struct.null)),
        footprint = foot.is_singleton(src)
    )

def points_to(struct, src, trgs, foots):
    if debug_encoding_enabled:
        assert(len(trgs) == len(foots))
        assert(len(trgs) == len(struct.points_to_fields))
        assert(isinstance(src, ExprRef))
        assert(all(isinstance(trg, ExprRef) for trg in trgs))
        assert(all(isinstance(foot, generic.Set) for foot in foots))

    msg = "Generating points to constraint for {} {} wrt footprints {}"
    logger.debug(msg.format(struct, src, foots))

    ptrs = zip(struct.points_to_fields, trgs)
    return SplitEncoding(
        structure = And([Not(src == struct.null)] +
                        [trg == struct.heap_fn(fld)(src) for fld, trg in ptrs]),
        footprint = LAnd([foot.is_singleton(src) for foot in sorted(foots,key=str)])
    )

def apply_to_shared(fun, fps_left, fps_right, fps_parent = None):
    # TODO: Especially if we drop the asserts, there are of course shorter ways to write this
    fps_left_dict, fps_right_dict, fps_parent_dict = (
        map(to_fp_dict, (fps_left, fps_right, fps_parent))
    )
    if fps_parent_dict is not None:
        #logger.debug("Parent: {}".format(fps_parent_dict))
        #logger.debug("Left: {}".format(fps_left_dict))
        #logger.debug("Right: {}".format(fps_right_dict))
        for child in (fps_left_dict, fps_right_dict):
            assert(set(fps_parent_dict.keys()).issuperset(child.keys()))

    left_keys = set(fps_left_dict.keys())
    right_keys = set(fps_right_dict.keys())
    shared_keys = left_keys.intersection(right_keys)
    #nonshared_keys = left_keys.symmetric_difference(right_keys)

    for k in shared_keys:
        assert(isinstance(k, tuple) and len(k) == 2)
        assert(isinstance(k[0], struct_mod.Struct))
        assert(isinstance(k[1], str))
        # The key is in both dictionaries => Apply constraint function
        if fps_parent_dict is None:
            yield fun(fps_left_dict[k], fps_right_dict[k])
        else:
            yield fun(fps_left_dict[k], fps_right_dict[k], fps_parent_dict[k])

    if fps_parent_dict is not None:
        # Non-shared constraints must just be propagated
        for fp_dict, keys in ((fps_left_dict, left_keys.difference(right_keys)),
                              (fps_right_dict, right_keys.difference(left_keys))):
            for k in keys:
                yield fps_parent_dict[k].is_identical(fp_dict[k])


    # for k, fps in fps_left_dict.items():
    #     assert(isinstance(k, tuple) and len(k) == 2)
    #     assert(isinstance(k[0], struct_mod.Struct))
    #     assert(isinstance(k[1], str))

    #     if k in fps_right_dict:
    #         # The key is in both dictionaries => Make constraint
    #         if fps_parent_dict is None:
    #             yield fun(fps_left_dict[k], fps_right_dict[k])
    #         else:
    #             yield fun(fps_left_dict[k], fps_right_dict[k], fps_parent_dict[k])

def disjointness(fps_left, fps_right):
    def assert_disjoint(left, right):
        assert(isinstance(left, generic.Set))
        assert(isinstance(right, generic.Set))
        return left.disjoint_from(right)

    return list(apply_to_shared(assert_disjoint, fps_left, fps_right))

def union(fps_left, fps_right, parent_fps):
    def assert_union(left, right, parent):
        for fp_set in (left, right, parent):
            assert(isinstance(fp_set, generic.Set))
        return parent.union_of(left, right)

    return list(apply_to_shared(assert_union, fps_left, fps_right, parent_fps))

def same_fps(fps_left, fps_right, parent_fps):
    fps_left = to_fp_dict(fps_left)
    fps_right = to_fp_dict(fps_right)
    if bool(fps_left) and bool(fps_right) and set(fps_left.keys()) != set(fps_right.keys()):
        # If both footprint sets are given, this means neither of the operands is 'emp' /
        # a spatial (dis)equality.
        # In that case, there can only be a model if we're talking about the same footprints
        logger.info("Warning: Conjunction cannot be satisfiable because of footprints over different fields:")
        if logger.debug_logging_enabled():
            logger.debug("Left: {}".format(fps_left))
            logger.debug("Right: {}".format(fps_right))
        return [Or()] # TODO: Other way to get False BoolRef from z3 than Or()?

    def assert_same(left, right, parent):
        for fp_set in (left, right, parent):
            assert(isinstance(fp_set, generic.Set))
        # TODO: More efficient encoding that doesn't use parent fps
        return And(parent.is_identical(left), parent.is_identical(right))

    return list(apply_to_shared(assert_same, fps_left, fps_right, parent_fps))

def either_fp(fps_left, fps_right, parent_fps):
    def assert_either(left, right, parent):
        for fp_set in (left, right, parent):
            assert(isinstance(fp_set, generic.Set))
        return Or(parent.is_identical(left), parent.is_identical(right))

    return list(apply_to_shared(assert_either, fps_left, fps_right, parent_fps))
