"""Direct (rather than unfolding) encoding of data structures.

.. testsetup::

   from sloth import *
   from sloth.encoder import constraints
   from sloth.encoder.direct import *
   sort = LambdaBackend.make_loc_sort(None)
   fpsort = sort.set_sort()

"""

# FIXME: Ensure that the names x0, ... r1, ... etc are unused!

import itertools

import z3

from ..backend import LambdaBackend, generic, lambdas, symbols
from ..utils import utils
from ..z3api import rewriter
from . import constraints as c
from . import slast
from .shared import *

def non_identical(x_i, x_j):
    # For some reason x_i is not x_j doesn't appear to do the right thing
    return str(x_i) != str(x_j)

def x(sort, i):
    """Get the i-th dedicated location variable"""
    assert(isinstance(sort, generic.SlSort))
    return sort['x{}'.format(i)]

def xs(sort, n):
    """
    >>> list(xs(sort, 3))
    [x0, x1, x2]
    """
    return (x(sort, i) for i in range(n))

def xs_set(sort, n):
    """
    >>> xs_set(sort, 3) # doctest: +NORMALIZE_WHITESPACE
    Store(Store(Store(K(Int, False), x0, True), x1, True), x2, True) : SET(Int)
    """
    return lambdas.LambdaSet.to_set(sort, *(x(sort, i) for i in range(n)))

def X(sort, fld = None):
    """Return the global FP variable for the given field.

    If no field is given, return the variable for the union.
    """
    assert isinstance(sort, generic.SlSort), "{} of type {} isn't a sort".format(sort, type(sort).__name__)
    suffix = fld if fld is not None else ''
    return sort.set_sort()['X' + suffix]

def Xs(sort, structs):
    yield X(sort)
    flds = set()
    for s in structs:
        for f in s.fields:
            if f not in flds:
                flds.add(f)
                yield X(sort, f)


def r(sort, k):
    """Return the k-th reachability predicate symbol.

    >>> type(r(sort, 3)(sort['x'], sort['y'])).__name__
    'BoolRef'
    """
    return z3.Function('r{}'.format(k), sort.ref, sort.ref, z3.BoolSort())

def rs(sort, n):
    return (r(sort, k) for k in range(1, n+1))

def is_bounded_heap_interpretation(n, structs):
    """Delta_SL^N: Define SL* heap interpretations of size at most N

    >>> delta = is_bounded_heap_interpretation(3, [sl.list.struct, sl.tree.struct])
    >>> print(delta)
    ;; Delta_SL(3)
    (And
      ;; Global FP is the union of all field FPs
      (X == Map(or, Map(or, Map(or, Xdata, Xleft), Xnext), Xright))
      ;; Global FP is subset of {x_1,...x_n}
      (Map(=>,
          X,
          Store(Store(Store(K(Int, False), x0, True), x1, True),
                x2,
                True)) ==
      K(Int, True))
      ;; Null is not allocated
      (Not(X[sl.list.null]))
      ;; Null is not allocated
      (Not(X[sl.tree.null]))
      ;; Field FPs for sl.list and sl.tree don't overlap
      (K(Int, False) == Map(and, Xnext, Xleft))
      ;; Field FPs for sl.list and sl.tree don't overlap
      (K(Int, False) == Map(and, Xnext, Xright))
    )

    """
    sort = {struct.sort for struct in structs}
    assert len(sort) == 1, \
        "Got sorts {}, but currently no direct encoding for multi-sort backends".format(sort)
    sort = sort.pop()

    cs = c.ConstraintList()

    # Union constraint for all fields including data fields
    flds = sorted(set(utils.flatten(s.fields for s in structs)), key=str)
    xfs = (X(sort, fld) for fld in flds)
    cs.append_expr(X(sort).is_union_of_all(*xfs),
                   description = 'Global FP is the union of all field FPs')

    xs = xs_set(sort, n)
    cs.append_expr(X(sort).subset_of(xs),
                   description = 'Global FP is subset of {x_1,...x_n}')

    for s in structs:
        cs.append_expr(z3.Not(X(sort).contains(s.null)),
                                description = 'Null is not allocated')

    # Disjointness constraints only for structural fields
    for i in range(len(structs)):
        for j in range(i+1, len(structs)):
            for f in structs[i].structural_fields:
                for g in structs[j].structural_fields:
                    desc = "Field FPs for {} and {} don't overlap".format(structs[i].name, structs[j].name)
                    cs.append_expr(X(sort, f).disjoint_from(X(sort, g)),
                                            description = desc)

    return cs.to_conjunction(description = 'Delta_SL({})'.format(n))

def is_stop_node(struct, x, *stops):
    """Return constraint that `x` is a stop node.

    `x` is a stop node if it's equal to null or any of the nodes in `stops`

    >>> print(is_stop_node(sl.tree.struct, sort['x'], sort['y'], sort['z']))
    ;; x is a stop node
    (Or
      (x == sl.tree.null)
      (x == y)
      (x == z)
    )

    """
    cs = c.ConstraintList()
    cs.append_expr(x == struct.null)
    for stop in stops:
        cs.append_expr(x == stop)
    desc = '{} is a stop node'
    return cs.to_disjunction(description = desc.format(x))

def S(struct, x, y):
    """Successor relation for `x` and `y` w.r.t. `flds`.

    >>> print(S(sl.tree.struct, sort['x'], sort['y']))
    ;; y is a ['left', 'right']-successor of x
    (Or
      (And(Xleft[x], sl.tree.left(x) == y))
      (And(Xright[x], sl.tree.right(x) == y))
    )

    """
    flds = struct.structural_fields
    exprs = [z3.And(X(struct.sort, fld).contains(x),
                    struct.heap_fn(fld)(x) == y)
             for fld in flds]
    cs = c.from_list(exprs)
    desc = '{} is a {}-successor of {}'.format(y, flds, x)
    return cs.to_disjunction(description = desc)

def R(n, k, struct, Z, *stops):
    """Define r_k as the k-step reachability relation within the footprint z.

    >>> Z = sl.tree.struct.fp_sort['Z']
    >>> print(R(3, 1, sl.tree.struct, Z)) # doctest: +ELLIPSIS
    ;; Interpret r1 as 1-step reachability
    (And
      ;; 1-step reachability from x0 to x0
      ...
      ;; 1-step reachability from x0 to x1
      (Iff
        (r1(x0, x1))
        (And
          (Z[x0])
          (Not
            ;; x1 is a stop node
            (Or
              (x1 == sl.tree.null)
            )
          )
          ;; x1 is a ['left', 'right']-successor of x0
          (Or
            (And(Xleft[x0], sl.tree.left(x0) == x1))
            (And(Xright[x0], sl.tree.right(x0) == x1))
          )
        )
      )
      ...
      ;; 1-step reachability from x2 to x2
      (Iff
        (r1(x2, x2))
        (...)
      )
    )
    >>> print(R(3, 3, sl.tree.struct, Z)) # doctest: +ELLIPSIS
    ;; Interpret r3 as 3-step reachability
    (And
      ;; 3-step reachability from x0 to x0
      ...
      ;; 3-step reachability from x0 to x1
      (Iff
        (r3(x0, x1))
        (Or(r2(x0, x1),
           Or(And(r2(x0, x0), r1(x0, x1)),
              And(r2(x0, x1), r1(x1, x1)),
              And(r2(x0, x2), r1(x2, x1)))))
      )
      ...
      ;; 3-step reachability from x2 to x2
      (Iff
        (r3(x2, x2))
        (Or(r2(x2, x2),
           Or(And(r2(x2, x0), r1(x0, x2)),
              And(r2(x2, x1), r1(x1, x2)),
              And(r2(x2, x2), r1(x2, x2)))))
      )
    )


    """
    assert n >= k >= 1
    sort = struct.sort
    if k == 1:
        exprs = [c.Iff(r(sort, 1)(x_i,x_j),
                       c.And(Z.contains(x_i),
                             c.Not(is_stop_node(struct, x_j, *stops)),
                             S(struct, x_i, x_j)),
                       description = '1-step reachability from {} to {}'.format(x_i, x_j))
                 for x_i, x_j in itertools.product(xs(sort, n), repeat = 2)
                 # Note: To be able to check acyclicity, we have to compute reachability even for x_i=x_j
                 #if non_identical(x_i, x_j)
        ]
    else:
        def step(x_i, x_j):
            exprs = [z3.And(r(sort, k-1)(x_i, x_k), r(sort, 1)(x_k, x_j))
                     for x_k in xs(sort, n)]
            return symbols.LOr(exprs)

        exprs = [c.Iff(r(sort, k)(x_i,x_j),
                       z3.Or(r(sort, k - 1)(x_i,x_j),
                             step(x_i, x_j)),
                       description = '{}-step reachability from {} to {}'.format(k, x_i, x_j))
                 for x_i, x_j in itertools.product(xs(sort, n), repeat = 2)
                 # Note: To be able to check acyclicity, we have to compute reachability even for x_i=x_j
                 #if non_identical(x_i, x_j)
        ]
    cs = c.from_list(exprs)
    desc = 'Interpret {} as {}-step reachability'.format(r(sort, k), k)
    return cs.to_conjunction(description = desc)

def reach(n, struct, Z, *stops):
    """
    >>> print(reach(3, sl.tree.struct, Z))
    ;; Define reachability predicates
    (And
      ;; Interpret r1 as 1-step reachability
      ...
      ;; Interpret r2 as 2-step reachability
      ...
      ;; Interpret r3 as 3-step reachability
      ...
    )

    """
    exprs = [R(n, k+1, struct, Z, *stops) for k in range(n)]
    #exprs = [struct.null == struct.null]
    cs = c.from_list(exprs)
    return cs.to_conjunction(description = 'Define reachability predicates')

def defn(n, struct, Z, root, *stops):
    """Define the footprint set `Z` w.r.t. root node `r`.

    >>> print(defn(3, sl.tree.struct, Z, sort['r']))
    ;; Define the footprint set Z : SET(Int) for root r and nodes x0,...,x2
    (And
      ;; Z : SET(Int) is a subset of {x0,...,x2}
      ...
      ;; If the root is a stop node, Z : SET(Int) is empty
      ...
      ;; Everything in Z : SET(Int) is reachable from the root r
      ...
    )


    """
    sort = struct.sort
    cs = c.ConstraintList()
    # Footprint Z contains only the n allowed locations
    cs.append_expr(Z.subset_of(xs_set(sort, n)),
                   description = '{} is a subset of {{{},...,{}}}'.format(Z, x(sort,0), x(sort,n-1)))
    # If the root is a stop node, Z is empty
    cs.append_constraint(
        c.Implies(is_stop_node(struct, root, *stops), Z.is_empty(),
                  description = 'If the root is a stop node, {} is empty'.format(Z))
    )
    # If the root isn't a stop node, all nodes in Z are reachable from the root
    exprs = [
        c.Implies(Z.contains(x_i), z3.Or(x_i == root, r(sort, n)(root, x_i)))
        for x_i in xs(sort, n)
    ]
    reach_cs = c.from_list(exprs)
    cs.append_constraint(
        reach_cs.to_conjunction(description = 'Everything in {} is reachable from the root {}'.format(Z, root))
    )

    return cs.to_conjunction(description = 'Define the footprint set {} for root {} and nodes {},...,{}'.format(Z, root, x(sort, 0), x(sort, n-1)))

def parents(n, struct, Z):
    """parents_N: No two parents have the same child.

    >>> print(parents(3, sl.tree.struct, Z)) # doctest: +ELLIPSIS
    ;; parents_N: No two parents have the same child
    (And
      ;; If a node has two identical successors they are both null
      (And
        (Implies(Z[x0],
                Implies(sl.tree.left(x0) == sl.tree.right(x0),
                        sl.tree.left(x0) == sl.tree.null)))
        ...
      )
      ;; If two nodes share a successor it's null
      (And
        (Implies(And(Z[x0], Z[x1], Not(x0 == x1)),
                And(Implies(sl.tree.left(x0) == sl.tree.left(x1),
                            sl.tree.left(x0) == sl.tree.null),
                    Implies(sl.tree.left(x0) == sl.tree.right(x1),
                            sl.tree.left(x0) == sl.tree.null),
                    Implies(sl.tree.right(x0) == sl.tree.left(x1),
                            sl.tree.right(x0) == sl.tree.null),
                    Implies(sl.tree.right(x0) == sl.tree.right(x1),
                            sl.tree.right(x0) == sl.tree.null))))
        ...
      )
    )

    """
    flds = struct.structural_fields
    sort = struct.sort

    ls = []

    if not struct.is_linear():
        # Ensure that if a node has the same successor twice, they are both null
        # This only makes sense for branching structures
        exprs = [z3.Implies(Z.contains(x_i),
                        symbols.LAnd([
                            z3.Implies(struct.heap_fn(f)(x_i) == struct.heap_fn(g)(x_i),
                                       struct.heap_fn(f)(x_i) == struct.null)
                            for f,g in itertools.combinations(flds, 2)
                        ]))
                 for x_i in xs(sort, n)]
        cs_single = c.from_list(exprs)
        ls.append(
            cs_single.to_conjunction(description = 'If a node has two identical successors they are both null')
        )

    def all_succs_different(x_i, x_j):
        return symbols.LAnd(
            [z3.Implies(struct.heap_fn(f)(x_i) == struct.heap_fn(g)(x_j),
                        struct.heap_fn(f)(x_i) == struct.null)
             for f,g in itertools.product(flds, repeat = 2)]
        )

    exprs2 = [
        z3.Implies(z3.And(Z.contains(x_i), Z.contains(x_j), z3.Not(x_i == x_j)),
                   all_succs_different(x_i, x_j))
        for x_i, x_j in itertools.combinations(xs(sort, n), 2)
    ]
    cs_double = c.from_list(exprs2)
    ls.append(cs_double.to_conjunction(description = "If two nodes share a successor it's null"))

    return c.And(
        *ls,
        description = 'parents_N: No two parents have the same child'
    )


def is_acyclic(n, struct, root, Z):
    """The structure rooted in `root` restricted to footprint `Z` is acyclic.

    >>> print(is_acyclic(3, sl.tree.struct, sort['r'], Z)) # doctest: +ELLIPSIS
    ;; acyclic_N: No cycles in the structure induced by Z : SET(Int)
    (And
      ;; parents_N: No two parents have the same child
      ...
      ;; There is no cycle from the root to the root
      (Not
        (r3(r, r))
      )
    )

    """
    sort = struct.sort
    if n > 1:
        ls = [parents(n, struct, Z)]
    else:
        ls = []
    ls.append(c.Not(r(sort, n)(root, root), description = 'There is no cycle from the root to the root'))
    cs = c.from_list(ls)
    return cs.to_conjunction(
        description = 'acyclic_N: No cycles in the structure induced by {}'.format(Z)
    )

def is_struct_footprint(n, struct, Z, y):
    """Tie `Z` to the global footprint vector `y`

    >>> y = FPVector(fpsort, prefix = 'Y', flds = 'next left right data'.split())
    >>> print(is_struct_footprint(3, sl.tree.struct, Z, y))
    ;; Z : SET(Int) equals the global footprints for sl.tree
    (And
      ;; Z : SET(Int) contains only sl.tree locations
      (Map(=>, Z, Map(and, Map(and, Xdata, Xleft), Xright)) ==
      K(Int, True))
      ;; All sl.tree footprints equal Z : SET(Int)
      (And
        (Z == Ydata)
        (Z == Yleft)
        (Z == Yright)
      )
      ;; All other footprints are empty
      (And
        (Ynext == K(Int, False))
      )
    )

    """
    assert isinstance(y, FPVector)
    sort = struct.sort
    intersection = lambdas.LambdaSet.intersection_of_all(
        sort,
        *(X(sort, fld) for fld in sorted(struct.fields))
    )
    subset = c.as_constraint(
        Z.subset_of(intersection),
        description = '{} contains only {} locations'.format(Z, struct.name)
    )
    equal_exprs = [Z.is_identical(fp) for fp in y.fps_for_struct(struct)]
    struct_equals = c.from_list(equal_exprs)
    ls = [
        subset,
        struct_equals.to_conjunction(description = 'All {} footprints equal {}'.format(struct.name, Z)),
    ]
    empty_exprs = [fp.is_empty() for fp in y.fps_for_other_structs(struct)]
    if empty_exprs:
        other_empty = c.from_list(empty_exprs)
        ls.append(other_empty.to_conjunction(description = 'All other footprints are empty'))

    combined = c.from_list(ls)
    return combined.to_conjunction('{} equals the global footprints for {}'.format(Z, struct.name))

def root_alloced_or_stop(Z, root, stop):
    expr = z3.Or(
        Z.contains(root),
        root == stop
    )
    return c.as_constraint(expr, description = 'The root {} is allocated or equal to {}'.format(root, stop))

def stop_node_occurs(n, struct, Z, stop):
    return c.Or(
        Z.is_empty(),
        *[c.And(Z.contains(x_i),
                symbols.LOr([stop == struct.heap_fn(fld)(x_i)
                             for fld in struct.structural_fields]),
                description = '{} is alloced and one of its successors is stop node {}'.format(x_i, stop))
          for x_i in xs(struct.sort, n)],
        description = 'If the {} is non-empty, it contains the stop node {}'.format(struct.unqualified_name, stop)
    )

def all_leaves_are_stop_nodes(n, Z, struct, *stops):
    sort = struct.sort
    fld_fns = [(fld, struct.heap_fn(fld)) for fld in struct.structural_fields]
    exprs = [c.Implies(
        z3.And(Z.contains(x_i), z3.Not(Z.contains(fld_fn(x_i)))),
        is_stop_node(struct, fld_fn(x_i), *stops),
        description = "If the {}-successor of {} isn't alloced it's a stop node".format(fld, x_i))
             for x_i in xs(sort, n)
             for fld, fld_fn in fld_fns]
    return c.from_list(exprs).to_conjunction('All leaves are stop nodes')

def stops_leaf_parent(n, x_p, struct, fld, stop):
    """`x_p` is a `fld`-ancestor of `stop`.

    >>> print(stops_leaf_parent(3, sort['x_p'], sl.tree.struct, 'right', sort['x_stop']))
    ;; x_p is a right-ancestor of the stop node x_stop
    (Or
      (sl.tree.right(x_p) == x_stop)
      ;; A right-descendant of x_p is the parent of the stop node x_stop
      (Or
        ;; x0 is the descendant that is the parent of x_stop
        (And
          (Or(x0 == sl.tree.right(x_p), r3(sl.tree.right(x_p), x0)))
          ;; x_stop is a ['left', 'right']-successor of x0
          (Or
            (And(Xleft[x0], sl.tree.left(x0) == x_stop))
            (And(Xright[x0], sl.tree.right(x0) == x_stop))
          )
        )
        ...
      )
    )
    """
    assert struct.unqualified_name == 'tree', \
        'Redundant stop point constraint for non-tree structure'
    sort = struct.sort
    f = struct.heap_fn(fld)

    descendant_cs = [
        c.And(
            z3.Or(x_c == f(x_p), r(sort, n)(f(x_p), x_c)),
            S(struct, x_c, stop),
            description = '{} is the descendant that is the parent of {}'.format(x_c, stop)

        )
        for x_c in xs(sort, n)
    ]
    descendant_constraint = c.from_list(descendant_cs).to_disjunction(
        description = 'A {}-descendant of {} is the parent of the stop node {}'.format(fld, x_p, stop)
    )

    return c.Or(
        f(x_p) == stop,
        descendant_constraint,
        description = '{} is a {}-ancestor of the stop node {}'.format(x_p, fld, stop)
    )

def stop_nodes_are_ordered_leaves(n, struct, Z, root, *stops):
    """If there are more than two `stops`, enforce that the stop nodes
occur in the same order in the tree induced by `Z` as in `stops`.

    >>> print(stop_nodes_are_ordered_leaves(3, sl.tree.struct, Z, sort['root'], sort['s1'], sort['s2'])) # doctest: +ELLIPSIS
    ;; All adjacent pairs of stop nodes in (s1, s2) are ordered in the induced tree of Z : SET(Int)
    (And
      ;; Stop nodes s1 and s2 have a LCA in Z : SET(Int)
      (Or
        ;; x0 is the LCA of s1 and s2
        (And
          (Z[x0])
          ;; x0 is a left-ancestor of the stop node s1
          (Or
            (sl.tree.left(x0) == s1)
            ;; A left-descendant of x0 is the parent of the stop node s1
            (Or
              ;; x0 is the descendant that is the parent of s1
              (And
                (Or(x0 == sl.tree.left(x0), r3(sl.tree.left(x0), x0)))
                ;; s1 is a ['left', 'right']-successor of x0
                (Or
                  (And(Xleft[x0], sl.tree.left(x0) == s1))
                  (And(Xright[x0], sl.tree.right(x0) == s1))
                )
              )
              ;; x1 is the descendant that is the parent of s1
              ...
              ;; x2 is the descendant that is the parent of s1
              ...
            )
          )
          ;; x0 is a right-ancestor of the stop node s2
          ...
        )
        ;; x1 is the LCA of s1 and s2
        ...
    )

    """
    if len(stops) <= 1:
        msg = 'Stop-node order constraints can only be generated for >= 2 stop nodes, but got {}'
        raise utils.SlothException(msg.format(len(stops)))
    else:
        sort = struct.sort

        def ordered_pair(s, t):
            exprs = [
                c.And(Z.contains(x_p),
                      stops_leaf_parent(n, x_p, struct, 'left', s),
                      stops_leaf_parent(n, x_p, struct, 'right', t),
                      description = '{} is the LCA of {} and {}'.format(x_p, s, t))
                for x_p in xs(sort, n)
            ]
            return c.from_list(exprs).to_disjunction(
                description = 'Stop nodes {} and {} have a LCA in {}'.format(s, t, Z)
            )

        cs_list = [
            ordered_pair(stops[k], stops[k+1])
            for k in range(len(stops)-1)
        ]

        return c.from_list(cs_list).to_conjunction(
            description = 'All adjacent pairs of stop nodes in {} are ordered in the induced tree of {}'.format(stops, Z)
        )

__alpha = symbols.data_pred_var(0)
__beta = symbols.data_pred_var(1)

def unary_data_pred_holds(n, struct, Z, pred):
    """Does the unary data predicate `pred` hold on `Z`?

    >>> print(unary_data_pred_holds(3, sl.tree.struct, Z, sl.alpha < 5))
    ;; The unary data predicate sl.alpha < 5 holds on Z : SET(Int)
    (And
      (Implies(Z[x0], sl.tree.data(x0) < 5))
      (Implies(Z[x1], sl.tree.data(x1) < 5))
      (Implies(Z[x2], sl.tree.data(x2) < 5))
    )

    """

    # TODO: Once we have fields as arrays rather than functions, we can simply map pred over the data field array -- if we convert pred into a function, that is
    sort = struct.sort
    def pred_holds_on(x_i):
        term = struct.heap_fn(struct.data_field)(x_i)
        return rewriter.partial_leaf_substitution(pred, {__alpha : term})

    cs = c.from_list([
        z3.Implies(Z.contains(x_i), pred_holds_on(x_i))
        for x_i in xs(sort, n)]
    )
    return cs.to_conjunction(
        description = 'The unary data predicate {} holds on {}'.format(pred, Z)
    )

def binary_data_pred_holds(n, struct, Z, fld, pred):
    """Does the binary data predicate `pred` hold on `Z`?

    >>> print(binary_data_pred_holds(3, sl.tree.struct, Z, 'left', sl.alpha < sl.beta))
    ;; The binary data predicate sl.alpha < sl.beta holds for left descendants in Z : SET(Int)
    (And
      ;; If x1 is a left-descendant of x0 then (sl.alpha < sl.beta)[sl.alpha/x0,beta/x1] holds
      (Implies(And(Z[x0],
                  Z[x1],
                  Or(r3(sl.tree.left(x0), x1),
                     sl.tree.left(x0) == x1)),
              sl.tree.data(x0) < sl.tree.data(x1)))
      ;; If x2 is a left-descendant of x0 then (sl.alpha < sl.beta)[sl.alpha/x0,beta/x2] holds
      ...
    )

    """

    sort = struct.sort
    def pred_holds_on(x_i, x_j):
        term = struct.heap_fn(struct.data_field)(x_i)
        term2 = struct.heap_fn(struct.data_field)(x_j)
        return rewriter.partial_leaf_substitution(pred, {__alpha : term,
                                                        __beta : term2})

    f = struct.heap_fn(fld)

    cs = c.from_list([
        c.as_constraint(
            z3.Implies(z3.And(Z.contains(x_i),
                              Z.contains(x_j),
                              z3.Or(r(sort, n)(f(x_i), x_j),
                                    f(x_i) == x_j)),
                       pred_holds_on(x_i, x_j)),
            description = 'If {x_j} is a {fld}-descendant of {x_i} then ({P})[{alpha}/{x_i},beta/{x_j}] holds'.format(x_i = x_i, x_j = x_j, P = pred, alpha = __alpha, beta = __beta, fld = fld)
        )
        for x_i,x_j in itertools.product(xs(sort, n), repeat = 2)
        if non_identical(x_i, x_j)]
    )
    return cs.to_conjunction(
        description = 'The binary data predicate {} holds for {} descendants in {}'.format(pred, fld, Z)
    )

def data_preds_hold(n, struct, Z, preds):
    unary = [unary_data_pred_holds(n, struct, Z, pred)
             for pred in preds.unary]
    binary = [binary_data_pred_holds(n, struct, Z, fld, pred)
              for fld, fld_preds in preds.binary.items()
              for pred in fld_preds]
    return c.from_list(unary + binary).to_conjunction(
        description = 'All data predicates hold')

def struct_encoding(n, Y, struct, Z, preds, root, *stops):
    assert preds is None or isinstance(preds, DataPreds)
    assert isinstance(Y, FPVector)
    cs_a = [is_struct_footprint(n, struct, Z, Y),
            is_acyclic(n, struct, root, Z),
            all_leaves_are_stop_nodes(n, Z, struct, *stops)
    ]
    if len(stops) > 1:
        cs_a.append(stop_nodes_are_ordered_leaves(n, struct, Z, root, *stops))
    else:
        try:
            stop = stops[0]
        except:
            stop = struct.null
        else:
            cs_a.append(stop_node_occurs(n, struct, Z, stop))
        cs_a.append(root_alloced_or_stop(Z, root, stop))
    if preds is not None:
        cs_a.append(data_preds_hold(n, struct, Z, preds))
    A = c.from_list(cs_a).to_conjunction('Structural encoding of list({}, {}) of size {} with data constraints {}'.format(root, stops, n, preds))
    cs_b = [reach(n, struct, Z, *stops),
            defn(n, struct, Z, root, *stops)
    ]
    B = c.from_list(cs_b).to_conjunction('Footprint encoding of list({}, {}) of size {}'.format(root, stops, n, preds))
    fresh_decls = set(itertools.chain([Z],
                                      xs(struct.sort, n),
                                      rs(struct.sort, n)))
    return SplitEnc(A, B, fresh_decls)

def call_encoding(config, call, Y):
    "Encode the given predicate call `call` w.r.t. the footprint `Y`."
    assert isinstance(call, slast.PredCall)
    assert isinstance(Y, FPVector)
    n = sum(config.bounds_by_struct.values())
    assert n > 0, 'No size bound defined in config'
    Z = config.get_fresh_fp()
    if call.pred is not None:
        dp = DataPreds((call.fld, call.pred))
    else:
        dp = None
    return struct_encoding(n, Y, call.struct, Z, dp, call.root, *call.stop_nodes)

def bounded_encoding(n, structs, Y, struct, Z, preds, root, *stops):
    "Top-level encoding of a formula that is a single predicate call."
    assert struct in structs
    A, B, _ = struct_encoding(n, Y, struct, Z, preds, root, *stops)
    return c.And(
        is_bounded_heap_interpretation(n,  structs),
        A,
        B
    )

def z3_input(n, Y, structs, struct, preds, root, *stops):
    """Generate a standalone Z3 input for the given call parameters.

    This is meant for testing individual calls, *not* for use inside
    the encoding of the entire separation logic. For the latter, see
    :func:`call_encoding` and :func:`is_bounded_heap_interpretation`.

    """
    Z = struct.fp_sort['Z']
    cs = bounded_encoding(n, structs, Y, struct, Z, preds, root, *stops)
    consts = ([root]
              + list(stops)
              + [struct.null for struct in structs]
              + [Z]
              + Y.all_fps()
              + list(xs(struct.sort, n))
              + list(Xs(struct.sort, structs)))
    funs = itertools.chain(*(s.heap_fns() for s in structs),
                           rs(struct.sort, n))
    decls = c.SmtDecls(consts, funs)
    return c.Z3Input(cs, decls = decls)
