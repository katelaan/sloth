"""Code for unrolling recursive predicates.

Contains methods for encoding on the fly (:func:`unroll`) and for
returning non-recursive but unencoded SL constraints
(:func:`unrolled_formulas`, :func:`unrolling_options`).

.. testsetup::

    from sloth import *
    from sloth.encoder.disjunctive import *

"""

import collections

from z3 import And, Or, ExprRef

from ..backend import symbols
from ..z3api import z3utils, rewriter
from ..utils import utils, logger

def get_child_const(struct, const, suffix):
    """Given a constant and a suffix, return new constant with concatenated name.

    >>> get_child_const(sl.tree.struct, sl.tree.loc("x"), "lr")
    xlr
    >>> get_child_const(sl.tree.struct, sl.tree.loc("x"), "lr").sort() == sl.tree.struct.sort.ref
    True

    """
    assert(isinstance(const, ExprRef))
    assert(isinstance(suffix, str))
    sort = struct.sort
    res = sort[str(const) + suffix]
    return res

def stop_node_partition(struct, stop_nodes):
        bf = len(struct.structural_fields)
        if bf == 1:
            return [[stop_nodes]]
        elif bf == 2:
            return [(stop_nodes[:i],stop_nodes[i:])
                    for i in range(len(stop_nodes)+1)]
        else:
            raise NotImplementedError("Branching factor != 1 or 2 not supported")

class UnrolledConstraint:
    def __init__(self, spatial, data, data_eq):
        for s in spatial:
            if not str(s).startswith("sl."):
                msg = "If you see this lovely message, something went wrong inside z3's internal expression DAG representation. So much fun!"
                raise utils.SlothException(msg)
        self.spatial = spatial
        self.data = data
        self.data_eq = data_eq
        #logger.debug("Created now constraint {}".format(self))

    def __add__(self, other):
        assert(isinstance(other, UnrolledConstraint))
        return UnrolledConstraint(
            self.spatial + other.spatial,
            self.data + other.data,
            self.data_eq + other.data_eq
        )

    def __repr__(self):
        return "UnrolledConstraint({!r}, {!r}, {!r})".format(self.spatial, self.data, self.data_eq)

def unrolling_iter(struct, depth, force_depth, root_prefix, data_pred_field = None, data_pred = None, stop_nodes = []):
    """Generates all unrollings of `struct` of depth at most `depth`.

    If `force_depth` is `True`, interprets the depth requirement as
    exact at any stage of the recursion, yielding a balanced structure
    of the given depth. `stop_nodes` is a list of stop nodes. It may
    be empty. Order of the stop nodes is enforced.

    >>> tree = sl.tree.struct
    >>> x = sl.tree.loc("x")
    >>> list(unrolling_iter(tree, 2, True, x)) # doctest: +ELLIPSIS, +NORMALIZE_WHITESPACE
    [(sl.sepcon(...)), [xl == sl.tree.left(x), ...])]
    >>> list(unrolling_iter(tree, 2, True, x, "left", sl.alpha > 2 * sl.beta)) # doctest: +ELLIPSIS, +NORMALIZE_WHITESPACE
    [(And(sl.sepcon(...)), xd > 2*xld), [xl == sl.tree.left(x), ..., xrd == sl.tree.data(xr)])]


    """
    for option in all_unrollings_as_lists(struct, depth, force_depth, root_prefix, data_pred_field, data_pred, stop_nodes):
        if bool(option.data):
            yield (symbols.LAnd([symbols.SepCon(option.spatial),
                                 symbols.LAnd(option.data)]),
                                option.data_eq)
        else:
            #logger.debug("Atoms: {}".format(option.spatial))
            yield (symbols.SepCon(option.spatial), option.data_eq)

def all_unrollings_as_lists(struct, depth, force_depth, root_prefix,
                            data_pred_field = None,
                            data_pred = None,
                            stop_nodes = [],
                            ancestor_data = [],
                            suffix = ""):
    """Generates pure and spatial part of all unrollings of `struct`.

    Yields (pure, spatial) tuples. Depth is limited to at most `depth`.

    If `force_depth` is `True`, interprets the depth requirement as
    exact at any stage of the recursion, yielding a balanced structure
    of the given depth. If `stop_nodes` is a non-empty list, generates
    all ways in which leaves can be instantiated to be the stop nodes
    in the correct order.

    >>> tree = sl.tree.struct
    >>> x, y, z = sl.tree.locs("x y z")
    >>> list(all_unrollings_as_lists(tree, 0, False, x))
    [UnrolledConstraint([sl.tree.eq(x, sl.tree.null)], [], [])]
    >>> list(all_unrollings_as_lists(tree, 1, False, x))
    [UnrolledConstraint([sl.tree.eq(x, sl.tree.null)], [], []), UnrolledConstraint([sl.tree.pointsto(x, xl, xr), sl.tree.eq(xl, sl.tree.null), sl.tree.eq(xr, sl.tree.null)], [], [xl == sl.tree.left(x), xr == sl.tree.right(x)])]
    >>> len(list(all_unrollings_as_lists(tree, 2, False, x)))
    5

    Forcing the (unique) balanced result via `force_depth`, e.g. the
    unique full tree of depth two with 4 comparisions and 3 pointers:

    >>> u = list(all_unrollings_as_lists(tree, 2, True, x))
    >>> len(u) == 1
    True
    >>> len(u[0].spatial) # Number of spatial atoms in the tree: 3 ptrs + 4 eqs
    7

    Options with `stop_nodes`:

    >>> list(all_unrollings_as_lists(tree, 1, False, x, None, None, [y,z]))
    [UnrolledConstraint([sl.tree.pointsto(x, xl, xr), sl.tree.eq(xl, y), sl.tree.eq(xr, z)], [], [xl == sl.tree.left(x), xr == sl.tree.right(x)])]
    >>> list(all_unrollings_as_lists(tree, 0, False, x, None, None, [y,z]))
    []
    >>> len(list(all_unrollings_as_lists(tree, 2, True, x, None, None, [y,z])))
    6

    Lists with `data_pred`:

    >>> ls = sl.list.struct
    >>> h = sl.list.loc("h")
    >>> list(all_unrollings_as_lists(ls, 2, False, h, None, sl.alpha == 42)) # doctest: +NORMALIZE_WHITESPACE
    [UnrolledConstraint([sl.list.eq(h, sl.list.null)], [], []),
     UnrolledConstraint([sl.list.pointsto(h, hn), sl.list.data(h, hd), sl.list.eq(hn, sl.list.null)], [hd == 42], [hn == sl.list.next(h), hd == sl.list.data(h)]),
     UnrolledConstraint([sl.list.pointsto(h, hn), sl.list.data(h, hd), sl.list.pointsto(hn, hnn), sl.list.data(hn, hnd), sl.list.eq(hnn, sl.list.null)], [hd == 42, hnd == 42], [hn == sl.list.next(h), hd == sl.list.data(h), hnn == sl.list.next(hn), hnd == sl.list.data(hn)])]
    >>> list(all_unrollings_as_lists(ls, 2, False, h, "next", sl.alpha < sl.beta)) # doctest: +NORMALIZE_WHITESPACE
    [UnrolledConstraint([sl.list.eq(h, sl.list.null)], [], []),
     UnrolledConstraint([sl.list.pointsto(h, hn), sl.list.data(h, hd), sl.list.eq(hn, sl.list.null)], [], [hn == sl.list.next(h), hd == sl.list.data(h)]),
     UnrolledConstraint([sl.list.pointsto(h, hn), sl.list.data(h, hd), sl.list.pointsto(hn, hnn), sl.list.data(hn, hnd), sl.list.eq(hnn, sl.list.null)], [hd < hnd], [hn == sl.list.next(h), hd == sl.list.data(h), hnn == sl.list.next(hn), hnd == sl.list.data(hn)])]

    Trees with `data_pred`

    >>> list(all_unrollings_as_lists(tree, 2, True, x, None, sl.alpha == 42)) # doctest: +NORMALIZE_WHITESPACE
    [UnrolledConstraint([...], [xd == 42, xld == 42, xrd == 42], [...])]
    >>> list(all_unrollings_as_lists(tree, 2, True, x, "left", sl.alpha > sl.beta))
    [UnrolledConstraint([...], [xd > xld], [...])]
    >>> list(all_unrollings_as_lists(tree, 2, True, x, "right", sl.alpha > (sl.beta + 17)))
    [UnrolledConstraint([...], [xd > xrd + 17], [...])]

    """

    #logger.debug("all_unrollings_as_lists({}, {}, {}, {}, {}, {}, {}, {!r})".format(struct, depth, force_depth, root_prefix, data_pred_field, data_pred, stop_nodes, suffix))
    assert(isinstance(depth, int))
    assert(isinstance(force_depth, bool))
    assert(isinstance(root_prefix, ExprRef))
    assert((data_pred_field is None) or isinstance(data_pred_field, str))
    assert((data_pred is None) or isinstance(data_pred, ExprRef))
    if data_pred_field is None:
        assert(data_pred is None or is_unary(data_pred))
    else:
        assert(not is_unary(data_pred))
    assert(isinstance(stop_nodes, list))
    assert(isinstance(suffix, str))

    root = get_child_const(struct, root_prefix, suffix)

    def apply_option(config, data_const):
        #logger.debug("Generating options {}".format(config))
        if len(config) == 0:
            yield UnrolledConstraint([], [], [])
        else:
            child_root, stop_nodes, fld = config[0]
            if data_const is None:
                new_ancestor_data = list(ancestor_data)
            else:
                new_ancestor_data = ancestor_data + [(fld,data_const)]
            # For each way to unfold child 1,...,n...
            for other in apply_option(config[1:], data_const):
                # For each way to unfold the first child...
                for this in all_unrollings_as_lists(struct, depth-1, force_depth,
                                                    root_prefix,
                                                    data_pred_field,
                                                    data_pred,
                                                    stop_nodes = stop_nodes,
                                                    ancestor_data = new_ancestor_data,
                                                    suffix = suffix + str(child_root)[-1]):
                    #logger.debug("Currently: {}".format(this))
                    #logger.debug("Adding: {}".format(other))
                    #logger.debug("Config: {}".format(config))
                    #logger.debug("Data const: {}".format(data_const))
                    combined = this + other
                    if False not in combined.spatial:
                        # Filter out options where stop-node constraints are unsatisfiable
                        yield combined

    if not force_depth or depth == 0:
        # If depth isn't forced, unfolding of depth 0 is always an option
        if len(stop_nodes) == 0:
            yield UnrolledConstraint([struct.equality_predicate()(root, struct.null)], [], [])
        elif len(stop_nodes) == 1:
            yield UnrolledConstraint([struct.equality_predicate()(root, stop_nodes[0])], [], [])
        else:
            # if there are more than two stop nodes, this can't be a leaf, yield nothing
            pass
    if depth > 0:
        # For depth > 0, combine points-to constraint with recursive options
        child_roots = [get_child_const(struct, root_prefix, suffix + fld[0])
                       for fld in struct.points_to_fields]
        # Spatial call
        local_struct = [struct.points_to_predicate()(root, *child_roots)]
        # In case we're under negation, must enforce that the introduced vars are indeed interpreted as successors
        local_data_eq = [child == struct.heap_fn(fld)(root)
                         for child, fld in zip(child_roots, struct.points_to_fields)]
        local_data = []
        if data_pred is not None:
            # Data call
            # Allocate data fields
            # FIXME: If we add data fields to structural points-to assertions, this part can go
            data_fld = struct.data_field
            # TODO: [DATA_CONST]
            data_const = get_child_const(struct, root_prefix, suffix + data_fld[0])
            #data_const = struct.heap_fn(data_fld)(root)
            #raise Exception("{} {}".format(data_const, data_const.__class__))
            local_struct.append(struct.fld_predicate(data_fld)(root, data_const))
            local_data_eq.append(data_const == struct.heap_fn(data_fld)(root))

            # Evaluate data predicate
            if is_unary(data_pred):
                local_data.append(apply_unary_pred(data_pred, data_const))
            else:
                # Compare against ancestors in whose data_pred_field-child-branch we are
                fld_ancestors = (ancestor for (fld, ancestor) in ancestor_data
                                 if fld == data_pred_field)
                local_data.extend(apply_binary_pred(data_pred, ancestor, data_const)
                                    for ancestor in fld_ancestors)
        else:
            data_const = None

        for stop_partition in stop_node_partition(struct, stop_nodes):
            assert(len(child_roots) == len(stop_partition))
            config = tuple(zip(child_roots, stop_partition, struct.points_to_fields))
            for child_constraints in apply_option(config, data_const):
                yield UnrolledConstraint(local_struct, local_data, local_data_eq) + child_constraints

def depth_options(num_children, curr_depth):
    if num_children == 1:
        for i in range(curr_depth):
            yield [i]
    else:
        for option in depth_options(num_children - 1, curr_depth):
            for i in range(curr_depth):
                yield option + [i]

alpha = symbols.data_pred_var(0)
beta = symbols.data_pred_var(1)

def is_unary(pred):
    return not z3utils.contains_const(beta, pred)

def apply_unary_pred(pred, arg):
    # TODO: [DATA_CONST]
    #assert(symbols.is_data_const(arg))
    return rewriter.partial_leaf_substitution(pred, {alpha : arg})

def apply_binary_pred(pred, fst, snd):
    assert(symbols.is_data_const(fst))
    assert(symbols.is_data_const(snd))
    return rewriter.partial_leaf_substitution(pred, {alpha : fst, beta : snd})
