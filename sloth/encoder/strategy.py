"""This module provides solution strategies.

.. testsetup::

   import functools
   from z3 import *
   from sloth import *
   from sloth.backend.symbols import SepCon
   from sloth.encoder.astbuilder import *
   from sloth.encoder.astutils import *
   from sloth.encoder.strategy import *

Let's try getting models for ordinary symbolic heaps:

>>> solve = functools.partial(solve_by_unfolding_strategy, sts)
>>> solve(sl.tree.pointsto("a", "b", "c"), 0)
Found model for unfolding []
Model [
  Struct sl.tree [
    ...
  ]
  Data [undefined]
]
>>> a, b = sl.list.locs("a", "b")
>>> m = solve(sl.list.neq(a, b), 0)
Found model for unfolding []
>>> eq(m.val_of(a), m.val_of(b))
False
>>> solve(sl.sepcon(sl.list.next("h","i"), sl.list.next("i","j")), 0)
Found model for unfolding []
...
>>> solve(sl.sepcon(sl.list.next("h","i"), sl.tree.pointsto("a", "b", "c")), 0)
Found model for unfolding []
Model [
  Struct sl.list [
    ...
  ]
  Struct sl.tree [
    ...
  ]
  Data [undefined]
]

If we use classical conjunction, the footprints of the arguments must
coincide. In the following simple example, this will force the
interpretation of h and i to coincide, too.

>>> h, i, j = sl.list.locs("h", "i", "j")
>>> m = solve(And(sl.list.next(h,i), sl.list.next(i,j)), 0)
Found model for unfolding []
>>> eq(m.val_of(h), m.val_of(i))
True

Whereas in this example, we get no model, because we're allocating
different fields:

>>> solve(And(sl.tree.left("t","u"), sl.tree.right("t","v")), 0)
Could not find model with current strategy.

With a separating conjunction, this works, of course:

>>> solve(sl.sepcon(sl.tree.left("t","u"), sl.tree.right("t","v")), 0)
Found model for unfolding []...

Disjunction works, too. Here, the solver can arbitrarily pick either
branch, so we can't make any assertions about (dis)equality between
locations.

>>> solve(Or(sl.list.next(h,i), sl.list.next(i,j)), 0)
Found model for unfolding []...

If we negate a pointer h ->_{next} i, we get a model with next(h) != i.

>>> m = solve(Not(sl.list.next(h,i)), 0)
Found model for unfolding []
>>> next_fn = m.struct_model(sl.list.struct).heap_fn("next")
>>> eq(next_fn(h), i) # doctest: +ELLIPSIS
False

Predicate calls are resolved via unfolding. List predicates:
>>> m = solve(sl.list(h), 1) # doctest: +ELLIPSIS
Found model for unfolding [(h, 0)]
>>> eq(m.val_of(h), m.val_of(sl.list.null))
True
>>> _ = solve(sl.sepcon(sl.list.seg(h, i), sl.list.neq(h, i)), 1)
Found model for unfolding [(h, 1)]
>>> _ = solve(sl.sepcon(sl.list.seg("a", "b"), sl.list.seg("b", "c")), 2)
Found model for unfolding [(a, 0), (b, 0)]
>>> _ = solve(sl.sepcon(sl.list.neq("a","c"),sl.sepcon(sl.list.seg("a", "b"), sl.list.seg("b", "c"))), 2)
Found model for unfolding [(a, 1), (b, 1)]
>>> _ = solve(sl.sepcon(sl.list("a"), sl.list.eq("a", sl.list.null)), 1)
Found model for unfolding [(a, 0)]
>>> _ = solve(sl.sepcon(sl.list("a"), sl.list.neq("a", sl.list.null)), 1)
Found model for unfolding [(a, 1)]

No models for contradictory constraints:

>>> solve(sl.sepcon(sl.list.pointsto("a","b"), sl.list.pointsto("a","b")), 1)
Could not find model with current strategy.
>>> solve(sl.sepcon(sl.list("x"), sl.sepcon(sl.list("x"), sl.list.neq("x", sl.list.null))), 3)
Could not find model with current strategy.

Tree predicates:

>>> _ = solve(sl.tree("t"), 1)
Found model for unfolding [(t, 0)]
>>> t, u, v = sl.tree.locs("t", "u", "v")
>>> m = solve(sl.tree.seg2(t, u, v), 1)
Found model for unfolding [(t, 1)]
>>> left_fn, right_fn = map(m.struct_model(sl.tree.struct).heap_fn, ("left", "right"))
>>> eq(left_fn(t), m.val_of(u)) and eq(right_fn(t), m.val_of(v))
True
>>> _ = solve(sl.sepcon(sl.tree.seg2("t", "u", "v"), sl.sepcon(sl.tree("u"), sl.tree("v"))), 1)
Found model for unfolding [(t, 1), (u, 1), (v, 1)]

Data (independent of predicate calls):

>>> d = Int("d")
>>> m = solve(And(sl.sepcon(sl.tree.pointsto("t", "u", "v"), sl.tree.data("t",d)), d == 42), 0)
Found model for unfolding []
>>> m.val_of(d)
42

Data predicate calls:

>>> a = sl.list.loc("a")
>>> m = solve(sl.sepcon(sl.list.neq(a, sl.list.null), sl.list.dpred.unary(sl.alpha > 9000, a)), 1)
Found model for unfolding [(a, 1)]
>>> data_fn = m.struct_model(sl.list.struct).heap_fn("data")
>>> z3_to_py(data_fn(m.val_of(a))) > 9000
True
>>> m = solve(sl.sepcon(sl.list.neq("a", sl.list.null), sl.list.dpred.next(sl.alpha < sl.beta, "a")), 1)
Found model for unfolding [(a, 1)]
>>> x, y, z, w = sl.list.locs("x", "y", "z", "w")
>>> d, e, f = Ints("d e f")
>>> expr = And(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y,z), sl.list.data(x,d), sl.list.data(y,e)), sl.list.dpred.next(sl.alpha < sl.beta, x))
>>> m = solve(expr, 3)
Found model for unfolding [(x, 2)]
>>> data_fn = m.struct_model(sl.list.struct).heap_fn("data")
>>> z3_to_py(data_fn(m.val_of(x))) < z3_to_py(data_fn(m.val_of(y)))
True
>>> expr = And(sl.sepcon(sl.list.pointsto(x, y), sl.sepcon(sl.list.pointsto(y, z), sl.list.pointsto(z, w), sl.list.data(x, d), sl.list.data(y, e), sl.list.data(z, f))), sl.list.dpred.next(sl.alpha < sl.beta, x))
>>> m = solve(expr, 3)
Found model for unfolding [(x, 3)]
>>> data_fn = m.struct_model(sl.list.struct).heap_fn("data")
>>> z3_to_py(data_fn(m.val_of(x))) < z3_to_py(data_fn(m.val_of(y)))
True
>>> z3_to_py(data_fn(m.val_of(y))) < z3_to_py(data_fn(m.val_of(z)))
True
>>> expr = And(sl.tree.dpred.right(sl.alpha > sl.beta, "t"), sl.sepcon(sl.tree.pointsto(t, u, v), sl.tree.data(t, d), sl.tree.pointsto(u, sl.tree.null, sl.tree.null), sl.tree.data(u, e), sl.tree.pointsto(v, sl.tree.null, sl.tree.null), sl.tree.data(v, f)))
>>> m = solve(expr, 3)
Found model for unfolding [(t, 2)]

Current limitations of the solver:

Currently, purely spatial predicates don't allocate the data
fields. That can be seen either as a bug or a feature. (Feature,
because this way we really support a "core" spatial logic in addition
to a logic with data.) I'm not sure yet if I want to keep it this way
or not. Of course you can force data allocation by providing a
tautological data predicate:

>>> _ = solve(sl.sepcon(sl.list.dpred.unary(sl.alpha == sl.alpha, "a"), sl.list.neq("a", sl.list.null)), 2)
Found model for unfolding [(a, 1)]

Nested negation:

>>> solve(Not(Not(sl.list("a"))), 1)
Traceback (most recent call last):
...
SlothException: Currently no support for nested negation

>>> solve(Not(Or(sl.list("a"), sl.list("b"))), 1)
Traceback (most recent call last):
...
SlothException: Currently only support for negation-normal form

"""

# TODO: Use this as example for incremental unfolding -- there's a solution at depth (1, 0)! solve(sl.sepcon(sl.list.seg("a", "b"), sl.list.seg("b", "c")), 2)

import z3

from .. import consts as consts_mod
from ..utils import utils, logger, timing
from ..model import model
from .. import z3api
from . import astbuilder, slast, encoder, utils as enc_utils, astutils

DEBUG_PRINT = True
INFO_PRINT = True

def strategy_debug_enabled():
    return DEBUG_PRINT and logger.debug_logging_enabled()

# TODO: Get rid of this global state once we don't need compatibility with the previous solver implementation
solver = None
prev_encoding = None

def decide(structs, expr, depth):
    global solver
    global prev_encoding
    solution = solve_by_unfolding_strategy(structs, expr, depth, None, False)
    return enc_utils.ResultState(solver, solution, prev_encoding)

def solve_by_unfolding_strategy(structs, expr, external_depth_bound, strategy = None, print_result = True):
    """Solve by uniformly replacing structures with disjunctive unfoldings.

    Depth is increased until a model is found or the external_depth_bound is
    reached.

    """
    slast.SlAst.id_ = [0] # Reset IDs to get consistent output
    slast.SlAst._id_dict = {} # Dict from sl exprs to ids to ensure that common sub exprs get the same IDs. (We cannot quite use a DAG instead, because we must in fact also assign identical IDs to predicate calls that only differ in data arguments.)
    ast = astbuilder.processed_ast(structs, expr)

    if strategy_debug_enabled():
        logger.debug(str(ast))
    # Get list of all the predicate calls that have to be unfolded
    pred_calls = astutils.pred_calls(ast)
    consts_by_struct = astutils.consts_by_struct(ast, structs)
    bound = compute_depth_bound(consts_by_struct, pred_calls)
    logger.info("Computed unfolding bound {}".format(bound))
    if bound > external_depth_bound:
        logger.info("Overriding with external depth bound {}".format(external_depth_bound))
        bound = external_depth_bound

    # By default, generate strategy that will try unfolding depth
    # 0,1,...,external_depth_bound, increasing the depth for each predicate call
    # simultaneously
    if strategy is None:
        strategy = unfold_uniformly_to_depth
    concrete_strategy = strategy(pred_calls, bound)
    # Apply strategy
    if strategy_debug_enabled():
        logger.debug("Expr: {}".format(expr))
        logger.debug("AST: {}".format(ast))
    return apply_strategy_to_ast(ast, concrete_strategy, print_result = print_result)

def compute_depth_bound(consts_by_struct, pred_calls):
    if not pred_calls:
        # No recursive calls, bound is always 0
        logger.info("No predicate calls => Nothing to unfold")
        return 0

    list_vars = 0
    tree_vars = 0
    data_preds = len([p for p in pred_calls if p.pred is not None])
    for struct, consts in consts_by_struct.items():
        if struct.unqualified_name == consts_mod.LIST_PRED:
            list_vars = _process_struct_consts(struct, consts)
        if struct.unqualified_name == consts_mod.TREE_PRED:
            tree_vars = _process_struct_consts(struct, consts)

    if INFO_PRINT:
        msg = "Formula contains {} list vars, {} tree vars, {} data predicate calls"
        logger.info(msg.format(list_vars, tree_vars, data_preds))
    # Note: Here I'm using an optimized bound, not having the data
    # preds below the multiplication
    return 2 * list_vars + 4 * tree_vars + 2 * data_preds

def _process_struct_consts(struct, consts):
    if True or strategy_debug_enabled():
        logger.info("Have the following {} vars: {}".format(struct.name, consts))
    var_count = len(consts)
    if any(z3.eq(v, struct.null) for v in consts):
        if True or strategy_debug_enabled():
            logger.info("Will not count null.")
        var_count -= 1
    return var_count


def solve_positive_without_disjunction(structs, expr, bound):
    """Tries specific unfoldings first before generating disjunctions.

    (Heuristic approach to simplify z3 input at the expense of
    increasing the number of solver calls.)

    Rationale: For positive formulas in the core theory, full trees
    always work as models. For positive formulas with data, usually
    either linear or full tree models work, either immediately below
    the root or beyond any prefix of the tree that is asserted
    separately.

    (E.g.: sl.tree(x) /\ sl.tree.pointsto(x,y,z) * sl.tree(y) * sl.tree(z))

    """
    raise NotImplementedError("TODO")

###############################################################################
# Unfolding strategies
###############################################################################

# TODO: Might do more sophisticated sorting by taking into account whether a tree root is also the source of a points-to assertion. (In which case we can skip depth 0 and )
# TODO: Do we always have to unroll predicates under negation until the full depth? I think so? Note that this is info is available in the processed_ast already!

def get_roots(pred_calls, sort_key = str):
    """Returns list of all roots of the given predicate calls.

    >>> aststs = functools.partial(ast, sts)
    >>> preds = list(map(aststs, [sl.tree("x"), sl.list("h"), sl.tree("a"), sl.list.seg("h", "t")]))
    >>> get_roots(preds)
    [a, h, x]
    >>> get_roots(preds, struct_arity_key(preds))
    [h, a, x]

    """
    unique_roots = set(pred.root for pred in pred_calls)
    return sorted(unique_roots, key = sort_key)

# TODO: This is currently suboptimal in get_roots, since we first throw the pred info away and then search it again to apply this sort function.
def struct_arity_key(preds):
    """Maps structure root to (structure branching factor, structure root).

    Use case: Provide as sort key when sorting roots to move lists to
    the front. Increasing list depth first makes sense, because
    unfolding lists is exponentially cheaper than unfolding trees.

    See :func:`get_roots` for an example.

    """
    def key_fun(root):
        f = lambda pred: z3.eq(pred.root, root)
        pred = utils.find_first(f, preds)
        # Prepend branching factor to prioritize linear structs in lexicographic sort
        return (pred.struct.branching_factor, str(root))
    return key_fun

def apply_strategy_to_ast(ast, strategy, print_result = False):
    global prev_encoding # Just for easy API compatibility with the old solver
    global solver
    solver = z3api.Solver()
    solved = False
    undefined = object()
    unfolding_dict = next(strategy, undefined)
    while (not solved) and (unfolding_dict is not undefined):
        timing.log(timing.EventType.StartSolver)
        # Unfold predicate calls (updating AST in place)
        if INFO_PRINT:
            logger.info("Trying unfolding {}".format(unfolding_dict))
        # Assemble encoding based on unfolding
        encoding = encoder.encode_ast(ast, unfolding_dict)
        prev_encoding = encoding
        if strategy_debug_enabled():
            logger.debug("STRATEGY: Full encoding:\n{!r}".format(encoding))
        # Try computing model
        if INFO_PRINT:
            logger.info("Starting z3...")
        model = model_if_sat(ast, encoding)
        timing.log(timing.EventType.EndSolver)
        solved = model is not None
        if not solved:
            unfolding_dict = next(strategy, undefined)
    if solved:
        if True:
            # Guarantee stable output for doctests
            standardized = sorted(unfolding_dict.items(),
                                  key = lambda x : str(x[0]))
            print("Found model for unfolding {}".format(standardized))
        return model
    else:
        if print_result: print("Could not find model with current strategy.")
        return None

def model_if_sat(ast, encoding):
    expr = encoding.full()
    timing.log(timing.EventType.StartSmt)
    if z3api.is_sat(expr):
        timing.log(timing.EventType.EndSmt)
        if INFO_PRINT:
            logger.info("z3 finished")
        consts = encoding.constants
        if consts is None:
            msg = "Constants not computed, can't construct model"
            raise utils.SlothException(msg)
        if strategy_debug_enabled():
            logger.debug(consts)
            logger.debug(z3api.model())
        return model.SmtModel(z3api.model(), consts, astutils.occurring_structs(ast))
    else:
        timing.log(timing.EventType.EndSmt)
        if INFO_PRINT:
            logger.info("z3 finished")
        return None

def unfold_uniformly_to_depth(pred_calls, max_depth):
    """Unfolding strategy that always increases all depths by one.

    >>> expr = sl.sepcon(sl.tree("a"), sl.list("b"))
    >>> calls = pred_calls(processed_ast(sts, expr))
    >>> for d in unfold_uniformly_to_depth(calls, 2): print(sorted(map(str,d.items())))
    ['(a, 0)', '(b, 0)']
    ['(a, 1)', '(b, 1)']
    ['(a, 2)', '(b, 2)']

    """
    roots = get_roots(pred_calls)
    for i in range(max_depth + 1):
        yield dict(utils.zip_with_const(roots, i))

def increase_unfolding_depth_incrementally(pred_calls, max_depth):
    """Unfolding strategy that increases depths one by one, starting with lists.

    >>> expr = sl.sepcon(sl.tree("a"), sl.list("b"))
    >>> calls = pred_calls(processed_ast(sts, expr))
    >>> for d in increase_unfolding_depth_incrementally(calls, 1): print(sorted(map(str,d.items())))
    ['(a, 0)', '(b, 0)']
    ['(a, 0)', '(b, 1)']
    ['(a, 1)', '(b, 1)']

    """

    # Move lists to the front for efficiency reasons
    roots = get_roots(pred_calls, struct_arity_key(pred_calls))
    depths = list(utils.zip_with_const(roots, 0))
    yield dict(depths)
    for i in range(max_depth):
        for j in range(len(depths)):
            depths[j] = (depths[j][0], i+1)
            yield dict(depths)
