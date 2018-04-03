import functools

import z3

from ..backend import symbols
from ..utils import utils, logger
from . import astbuilder, astutils, splitprims, disjunctive
from .utils import EncoderState
from .constset import ConstantSet
from .footprints import to_fp_dict, make_global_fps, make_fp, FootprintManager
from .slast import *
from ..z3api import z3utils

DEBUG_PRINT = True

def encoder_debug_enabled():
    return DEBUG_PRINT and logger.debug_logging_enabled()

def unfold_calls(ast, unfolding_dict):
    def f_inner(obj, child_results):
        # Unfolding takes place entirely in the leaves
        return None

    def f_leaf(obj):
        if obj.is_pred_call():
            apply_unfolding(obj, unfolding_dict)
        return None

    return astutils.fold(f_inner, f_leaf, ast)

def apply_unfolding(call, unfolding_dict, is_under_negation):
    if encoder_debug_enabled():
        logger.debug("UNFOLDING: Will unfold {!r}".format(call))

    # TODO: [Constants] Don't assign consts to call obj
    consts = ConstantSet([call.struct])

    # Make global fp constraint
    #prefix = call.fp_letter + str(call.id_) + "_"
    prefix = call.struct.unqualified_name + "." + str(call.root)
    for n in call.stop_nodes:
        prefix += "_" + str(n)
    prefix += "."

    call_fps = FootprintManager([call.struct], prefix).typed_fp_dict()
    # If this is not a data predicate, this doesn't have a data footprint
    if call.pred is None:
        del call_fps[(call.struct, call.struct.data_field)]
    for (struct,_), fp in call_fps.items():
        consts.add_fp_consts(struct, fp)

    asts = []
    encodings = []
    fp_constraints = []
    data_constraints = []
    # Explicit disjunction over all options. (I.e., without nesting.)
    # TODO: More efficient encoding (nested disjunction)
    for i, (constraint, data_eq) in enumerate(disjunctive.unrolling_iter(
            call.struct,
            depth = unfolding_dict[call.root],
            force_depth = False,
            root_prefix = call.root,
            data_pred_field = call.fld,
            data_pred = call.pred.to_sl_expr() if call.pred is not None else None,
            stop_nodes = call.stop_nodes
    )):
        if encoder_debug_enabled():
            logger.debug("Will build AST for constraint {}".format(constraint))
            logger.debug("Additional positive data equalities {}".format(data_eq))

        data_constraints.append(data_eq)
        # TODO: More understandable names of FP vars in unfolding? (Can e.g. assign to fp_letter -- dirty but simple and effective. Can even do that together with the id assignment in the preprocessing)
        unrolling_ast = astbuilder.processed_ast([call.struct], constraint)
        if encoder_debug_enabled():
            logger.debug("Built the AST")
        unrolling_encoding = encode_ast(unrolling_ast, unfolding_dict = {})
        assert(unrolling_encoding.has_split())
        unrolling_split = unrolling_encoding.split
        if encoder_debug_enabled():
            logger.debug("Encoded the AST")
            #logger.debug("That yielded\n{}".format(unrolling_split))
        consts = consts + unrolling_encoding.constants
        unrolling_fps = unrolling_ast.fps
        assert(isinstance(unrolling_fps, dict))

        # Stop nodes have to be pairwise different
        if len(call.stop_nodes) >= 2:
            # Currently only supporting at most two stop nodes
            assert(len(call.stop_nodes) == 2)
            unrolling_split.structure = And(unrolling_split.structure,
                                            Not(call.stop_nodes[0] == call.stop_nodes[1]))

        # Connect FPs of the unrolling with fps of the call
        if encoder_debug_enabled():
            logger.debug("Global FPs: {}".format(call_fps))
            logger.debug("Introduced FPs: {}".format(unrolling_fps))
        assert(set(call_fps.keys()).issuperset(set(unrolling_fps.keys())))
        fp_connection = []
        for k,v in call_fps.items():
            # Ensure that if a global FP has no local counterpart,
            # it's explicitly empty; and that otherwise, it's
            # identical to the local counterpart
            local_v = unrolling_fps.get(k, None)
            if local_v is None:
                fp_connection.append(v.is_empty())
            else:
                fp_connection.append(v.is_identical(local_v))
        if encoder_debug_enabled():
            logger.debug("Connecting FPs: {}".format(fp_connection))

        asts.append(unrolling_ast)
        encodings.append(unrolling_split)
        fp_constraints.append(symbols.LAnd(fp_connection))
        if encoder_debug_enabled():
            logger.debug("UNFOLDING of {} -- Constraint #{}: {}".format(call.to_sl_expr(), i, constraint))
            logger.debug("Encoding:\n{}".format(unrolling_encoding))
            logger.debug("Constants:\n{}".format(consts))

    if is_under_negation:
        for i, e in enumerate(encodings):
            #logger.debug("Option #{} prior to negation:\n{}".format(i, e))
            e.negate()
            #logger.debug("Negated option #{}:\n{}".format(i, e))

        if encoder_debug_enabled():
            logger.debug("Global FP constraint:\n{}".format(symbols.LOr(fp_constraints)))
        # Pair unrollings with negation of the global footprint constraint
        combined = []
        for i, (unrolling_split, fp_connection, data_eqs) in enumerate(zip(encodings, fp_constraints, data_constraints)):
            # Either the FP connection is false,
            # Or the (negated) encoding holds...

            # The negated encoding is only considered to hold if the
            # global meaning of the introduced data variables is
            # respected -- meaning the last structural node points to
            # null and the data constants are indeed the successors of
            # whatever node they were introduced for
            option = Or(Not(fp_connection), And(unrolling_split.structure,
                                                symbols.LAnd(data_eqs)))
            # option = Or(Not(fp_connection), And(unrolling_split.merged(),
            #                                     symbols.LAnd(data_eqs)))
            if encoder_debug_enabled():
                logger.debug("Option #{}:\n{}".format(i, option))
            combined.append(option)
        # ...but also, at least one of the fp connections holds
        all_union_constraints = symbols.LAnd(
            [option.footprint for option in encodings
             if option.footprint is not None]
        )
        if encoder_debug_enabled():
            logger.debug("All FP union constraints for {}:\n{}".format(call.to_sl_expr(), all_union_constraints))

        joined_split = splitprims.SplitEncoding(
            structure = symbols.LAnd(combined),
            footprint = And(
                # All the partial FP constraints hold (which is always possible)
                all_union_constraints,
                # And at the same time, one of the FP constraints must hold,
                # to establish the connection to the global FPs!
                symbols.LOr(fp_constraints)
            )
        )
    else:
        # Pair unrollings with the global footprint constraint
        for unrolling_split, fp_connection in zip(encodings, fp_constraints):
            unrolling_split.footprint = symbols.LAnd(
                [c for c in (unrolling_split.footprint, fp_connection)
                 if c is not None])

        # One of the unrollings must be true
        full_unrolling = symbols.LOr([e.merged() for e in encodings])
        # Make a trivial split. Since we're not under negation, the
        # split info will never be used anyway.
        joined_split = splitprims.SplitEncoding(
            structure = full_unrolling,
            footprint = None
        )

    call._state_transition(EncoderState.PreprocFinished, EncoderState.UnfoldingComputed)
    if encoder_debug_enabled():
        logger.debug("Done unfolding")
    return (call_fps, consts, joined_split)

class Encoding:
    def __init__(self, sl_expr, combined = None, split = None, fps = None, constants = None, is_negated = False, child_encodings = []):
        assert(combined is not None or split is not None)
        self.sl_expr = sl_expr
        self.split = split
        self.combined = combined
        self.fps = fps
        self.constants = constants
        self.is_negated = is_negated
        self.child_encodings = child_encodings

    def __str__(self):
        return "Encoding(\n{}\n)".format(self._attr_str())

    def _attr_str(self):
        strs = []
        for arg in [("sl_expr", self.sl_expr),
                    ("is_negated", self.is_negated),
                    ("fps", self.fps),
                    ("consts", self.constants),
                    ("combined", self.combined),
                    ("split", self.split)]:
            if arg[1] is not None:
                strs.append("  {} = {}".format(*arg))
        return "\n".join(strs)

    def __repr__(self):
        rep = "Encoding[\n" + self._attr_str()
        if self.child_encodings:
            rep += "\n  Children = ["
            for child in self.child_encodings:
                rep += "\n" + utils.indented(repr(child), 4)
            rep += "\n  ]"
        rep += "\n]"
        return rep

    def has_split(self):
        return self.split is not None

    def full(self):
        if self.combined is not None:
            return self.combined
        else:
            return self.split.merged()

def encode_ast(ast, unfolding_dict):
    inner_dict = {
        SlAnd : encode_and,
        SlOr : encode_or,
        SlNot : encode_not,
        SepCon: encode_sepcon,
    }
    leaf_dict = {
        PointsTo : encode_pto,
        PointsToSingleField : encode_pto_fld,
        SpatialEq : encode_eq,
        DataAtom : encode_data_atom,
        PredCall : functools.partial(encode_call, unfolding_dict)
    }

    next_id = 0

    def walk_ast(node, is_under_negation = False):
        if node.is_leaf():
            enc = leaf_dict[type(node)](node, is_under_negation)
            # Assign constants to encoding
            if not node.is_pred_call():
                cs = _leaf_constants(node, enc.fps)
                enc.constants = cs
            return enc
        else:
            if isinstance(node, SlNot):
                child_under_negation = not is_under_negation
            else:
                child_under_negation = is_under_negation
            child_results = [walk_ast(child, child_under_negation)
                             for child in node]
            enc = inner_dict[type(node)](node, *child_results, is_under_negation)
            # Assign constants to encoding
            cs = _inner_constants(node, enc.fps, *child_results)
            enc.constants = cs
            return enc

    return walk_ast(ast)

def _leaf_constants(obj, fps):
    assert(obj.state >= EncoderState.EncodingAssigned)
    # Constants of pred call are returned by unfolding
    assert(not obj.is_pred_call())
    try:
        structs = [obj.struct]
    except AttributeError:
        # Data atom => No structs
        assert(obj.is_data())
        structs = []
    cs = ConstantSet(structs)
    cs.add_data_consts(*obj.data_consts())
    try:
        cs.add_loc_consts(obj.struct, *obj.loc_consts())
        cs.add_fp_consts(obj.struct, *fps.values())
    except AttributeError:
        # Data atom => No structs => No locations/fps to add
        assert(obj.is_data())
    return cs


def _inner_constants(obj, fps, *child_encs):
    structs = astutils.occurring_structs(obj)
    cs = ConstantSet(structs)
    for (struct,_), fp in fps.items():
        assert(struct in structs)
        cs.add_fp_consts(struct, fp)
    for child_enc in child_encs:
        if child_enc.constants is None:
            msg = "Constants not set in {}"
            raise utils.SlothException(msg.format(child_enc))
        cs = cs + child_enc.constants
    return cs

def encoding_from_split_expr(ast, split, fps, is_negated):
    assert isinstance(ast, SlAst)
    # TODO: [Constants] Assign to ast here until we've decoupled const computation
    ast.fps = fps
    assert isinstance(split, splitprims.SplitEncoding)
    assert isinstance(fps, dict)
    ast._state_transition(EncoderState.PreprocFinished, EncoderState.EncodingAssigned)
    return Encoding(ast.to_sl_expr(), split = split, fps = fps, is_negated = is_negated)

def encoding_from_full_expr(ast, full, fps, is_negated):
    assert isinstance(ast, SlAst)
    # TODO: [Constants] Assign to ast here until we've decoupled const computation
    ast.fps = fps
    assert isinstance(full, z3.ExprRef)
    assert isinstance(fps, dict)
    ast._state_transition(EncoderState.PreprocFinished, EncoderState.EncodingAssigned)
    return Encoding(ast.to_sl_expr(), combined = full, fps = fps, is_negated = is_negated)

def encode_pto(pto, is_under_negation):
    # fps = { (pto.struct, fld) : make_fp(pto.struct, fld, str(pto.src) + str(pto.id_) + ".")
    #         for fld in pto.struct.points_to_fields }
    fps = { (pto.struct, fld) : make_fp(pto.struct, fld, str(pto.src) + ".")
            for fld in pto.struct.points_to_fields }
    split_encoding = splitprims.points_to(pto.struct, pto.src, pto.trg, fps.values())

    if is_under_negation:
        split_encoding.negate()
    return encoding_from_split_expr(pto, split_encoding, fps, is_under_negation)

def encode_pto_fld(pto, is_under_negation):
    #fp = make_fp(pto.struct, pto.fld, str(pto.src) + str(pto.id_) + ".")
    fp = make_fp(pto.struct, pto.fld, str(pto.src) + ".")
    fps = { (pto.struct, pto.fld) : fp }
    split_encoding = splitprims.fld_points_to(
        pto.struct, pto.fld, pto.src, pto.trg, fp
    )
    if is_under_negation:
        split_encoding.negate()
    return encoding_from_split_expr(pto, split_encoding, fps, is_under_negation)

def encode_call(unfolding_dict, call, is_under_negation):
    fps, consts, split_unfolding = apply_unfolding(call, unfolding_dict, is_under_negation)
    assert(call.state >= EncoderState.UnfoldingComputed)
    if call.pred is not None:
        # TODO: [Data consts] Should we manually add data constants here? This should force their inclusion in the model even at depth 0
        consts.add_data_consts(*call.data_consts())

    if encoder_debug_enabled():
        logger.debug("Overall encoding of {}:\n{}".format(call.to_sl_expr(), split_unfolding))

    enc = encoding_from_split_expr(call, split_unfolding, fps, is_under_negation)
    enc.constants = consts
    return enc

def encode_eq(eq, is_under_negation):
    fps = {} # => Behave like emp!
    split_encoding = splitprims.SplitEncoding(
        structure = eq.left == eq.right,
        footprint = None
    )
    if not (eq.negated == is_under_negation):
        split_encoding.negate()
    return encoding_from_split_expr(eq, split_encoding, fps, is_under_negation)

def encode_data_atom(da, is_under_negation):
    fps = {}
    split_encoding = splitprims.SplitEncoding(
        structure = da.atom,
        footprint = None
    )
    if is_under_negation:
        split_encoding.negate()
    return encoding_from_split_expr(da, split_encoding, fps, is_under_negation)

def encode_sepcon(sc, left_enc, right_enc, is_under_negation):
    fps = make_global_fps(sc, left_enc, right_enc)
    # TODO: Avoid introduction of True disjointness constraint in case there is no sharing between children
    disjointness = symbols.LAnd(splitprims.disjointness(left_enc.fps, right_enc.fps))
    union = symbols.LAnd(splitprims.union(left_enc.fps, right_enc.fps, fps))
    #logger.debug("SepCon disjointness: {}".format(disjointness))
    #logger.debug("SepCon union: {}".format(union))

    if is_under_negation:
        # A negated * is true in either of the following cases;
        # 1.) The left constraint is falsified
        # 2.) The right constraint is falsified
        # 3.) The disjointness criterion is violated.
        # Note that we don't negate the global footprint criterion
        assert(left_enc.is_negated)
        assert(right_enc.is_negated)
        assert(left_enc.has_split())
        assert(right_enc.has_split())
        # One of the structure constraints or the disjointness constraint are violated
        structure = Or(left_enc.split.structure,
                       right_enc.split.structure,
                       Not(disjointness))
        # All union constraints must continue to hold even under negation
        # That's always possible!
        footprint = symbols.LAnd([constraint
                                  for constraint in [union,
                                                     left_enc.split.footprint,
                                                     right_enc.split.footprint]
                                  if constraint is not None])
        #structure = Or(left_enc.full(), right_enc.full(), Not(disjointness))
        #footprint = union
    else:
        if encoder_debug_enabled():
            logger.debug("Left:\n{}".format(left_enc))
            logger.debug("Right:\n{}".format(right_enc))
        assert(left_enc.has_split())
        assert(right_enc.has_split())
        structure = And(left_enc.split.structure,
                        right_enc.split.structure,
                        disjointness)
        footprint = symbols.LAnd([fp
                                 for fp in (left_enc.split.footprint,
                                            right_enc.split.footprint,
                                            union)
                                  if fp is not None])

    split_encoding = splitprims.SplitEncoding(structure, footprint)
    if encoder_debug_enabled():
        logger.debug("SUMMARIZING SEPCON {}: encoded as follows:".format(sc.to_sl_expr()))
        logger.debug("Under negation: {}".format(is_under_negation))
        logger.debug("Global fps: {}".format(to_fp_dict(fps)))
        logger.debug("Left fps: {}".format(to_fp_dict(left_enc.fps)))
        logger.debug("Right fps: {}".format(to_fp_dict(right_enc.fps)))
        logger.debug("Global union constraint: {}".format(union))
        logger.debug("Full footprint: {}".format(footprint))
        logger.debug("Full structure: {}".format(structure))
        logger.debug("END SEPCON")

    enc = encoding_from_split_expr(sc, split_encoding, fps, is_under_negation)
    enc.child_encodings = [left_enc, right_enc]
    return enc


def encode_and(conj, left_enc, right_enc, is_under_negation):
    if is_under_negation:
        msg = "Currently only support for formulas in NNF"
        raise utils.SlothException(msg)

    # TODO: Improve top-level FP constraints for conjunction (not introducing new vars but arbitrarily passing on child constraints)
    # FIXME: Conjunction: Should return False if the children use different footprint sets, because this means that the children have footprints for different fields, meaning the conjunction cannot be satisfied! Is that already the case or not?
    fps = make_global_fps(conj, left_enc, right_enc)
    global_constraints = symbols.LAnd(splitprims.same_fps(left_enc.fps, right_enc.fps, fps))

    assert(left_enc.has_split())
    assert(right_enc.has_split())
    structure = And(left_enc.split.structure, right_enc.split.structure)
    fp_constraints = [fp for fp in (left_enc.split.footprint,
                                  right_enc.split.footprint,
                                  global_constraints)
                      if fp is not None]
    footprint = symbols.LAnd(fp_constraints)

    if encoder_debug_enabled():
        logger.debug("SUMMARIZING CONJUNCTION {}: encoded as follows:".format(conj.to_sl_expr()))
        logger.debug("Left fps: {}".format(to_fp_dict(left_enc.fps)))
        logger.debug("Right fps: {}".format(to_fp_dict(right_enc.fps)))
        logger.debug("Global fps: {}".format(to_fp_dict(fps)))
        logger.debug("Global FP constraint: {}".format(global_constraints))
        logger.debug("Full footprint:\n{}".format(footprint))
        logger.debug("Full structure:\n{}".format(structure))
        logger.debug("END CONJUNCTION")

    split_encoding = splitprims.SplitEncoding(structure, footprint)
    enc = encoding_from_split_expr(conj, split_encoding, fps, is_negated = False)
    enc.child_encodings = [left_enc, right_enc]
    return enc

def encode_or(disj, left_enc, right_enc, is_under_negation):
    if is_under_negation:
        msg = "Currently only support for formulas in NNF"
        raise utils.SlothException()

    fps = make_global_fps(disj, left_enc, right_enc)
    # Warning: We can't compute the split for Or, so we must directly build the encoding.
    fp_constraints = splitprims.either_fp(left_enc.fps, right_enc.fps, fps)
    global_fp_constraint = symbols.LAnd(fp_constraints)
    encoding = And(Or(left_enc.full(), right_enc.full()), global_fp_constraint)
    enc = encoding_from_full_expr(disj, encoding, fps, is_negated = False)
    enc.child_encodings = [left_enc, right_enc]
    return enc

def encode_not(neg, arg_enc, is_under_negation):
    if is_under_negation:
        msg = "Currently no support for nested negation"
        raise utils.SlothException(msg)

    # If the child already contains a negated encoding (which
    # is the case for predicate calls under negation, where we
    # do the negation "in place"), then we just return
    if not arg_enc.is_negated:
        msg = "{} is under negation, but its encoding is not negated"
        raise utils.SlothException(msg.format(arg_enc.sl_expr))

    if encoder_debug_enabled():
        logger.debug("Argument of negation {} is already negated".format(neg.arg.to_sl_expr()))

    neg_fps = make_global_fps(neg, arg_enc)
    arg_fps = arg_enc.fps

    if encoder_debug_enabled():
        logger.debug("Global FPs: {}".format(neg_fps))
        logger.debug("Child FPs: {}".format(arg_fps))

    assert(set(neg_fps.keys()).issuperset(set(arg_fps.keys())))

    fp_connection = [neg_fps[k].is_identical(arg_fps[k])
                     for k in arg_fps.keys()]
    if encoder_debug_enabled():
        logger.debug("Connecting FPs: {}".format(fp_connection))

    # The negation holds if its (already negated) argument holds,
    # in the (positive) global footprint The FP is not negated
    # because we only have top-level negation We need to tie the
    # negated formula to the the non-negated part E.g. ls(x) *
    # sorted_ls(y) /\ (not (sorted_ls(x) * ls(y)) should enforce
    # that ls(x) is unsorted. To have this effect, the negated
    # formula and the positive one have to be interpreted in the
    # same footprint!

    # Put the entire argument encoding into the structure part of
    # the split Note: This is only sound because there's no
    # nesting of 'not'.
    split_encoding = splitprims.SplitEncoding(
        structure = arg_enc.full(),
        footprint = symbols.LAnd(fp_connection)
    )
    if encoder_debug_enabled():
        logger.debug("Negation encoded as:\n{}".format(split_encoding))
    enc = encoding_from_split_expr(neg, split_encoding, neg_fps, is_negated = False)
    enc.child_encodings = [arg_enc]
    return enc
