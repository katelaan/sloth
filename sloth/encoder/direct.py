"""Direct (rather than unfolding) encoding of data structures.

.. testsetup::

   from sloth import *
   from sloth.encoder import constraints
   from sloth.encoder.direct import *
   sort = LambdaBackend.make_loc_sort(None)
   fpsort = sort.set_sort()

"""

import collections
import itertools
import operator

import z3

from . import constraints as c
from ..backend import LambdaBackend, generic, lambdas, symbols
from ..utils import utils
from ..z3api import rewriter

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

def is_bounded_heap_interpretation(n, sort, structs):
    """Delta_SL^N: Define SL* heap interpretations of size at most N

    >>> delta = is_bounded_heap_interpretation(3, LambdaBackend.make_loc_sort(None), [sl.list.struct, sl.tree.struct])
    >>> print(delta)
    ;; Delta_SL(3)
    (And
      ;; Global FP is the union of all field FPs
      (X == Map(or, Map(or, Xnext, Xleft), Xright))
      ;; Global FP is subset of {x_1,...x_n}
      (Store(Store(Store(K(Int, False), x0, True), x1, True),
            x2,
            True) ==
      Map(=>,
          X,
          Store(Store(Store(K(Int, False), x0, True), x1, True),
                x2,
                True)))
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
    cs = c.ConstraintList()
    flds = utils.flatten(s.structural_fields for s in structs)

    xfs = (X(sort, fld) for fld in flds)
    cs.append_expr(X(sort).is_union_of_all(*xfs),
                   description = 'Global FP is the union of all field FPs')

    xs = xs_set(sort, n)
    cs.append_expr(X(sort).subset_of(xs),
                   description = 'Global FP is subset of {x_1,...x_n}')

    for s in structs:
        cs.append_expr(z3.Not(X(sort).contains(s.null)),
                                description = 'Null is not allocated')

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
    #for s in structs:
    #    cs.append_expr(x == s.null)
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

def R(n, k, struct, z):
    """Define r_k as the k-step reachability relation within the footprint z.

    >>> z = sl.tree.struct.fp_sort['z']
    >>> print(R(3, 1, sl.tree.struct, z)) # doctest: +ELLIPSIS
    ;; Interpret r1 as 1-step reachability
    (And
      ;; 1-step reachability from x0 to x1
      (Iff
        (r1(x0, x1))
        (And
          (z[x0])
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
      ;; 1-step reachability from x2 to x1
      (Iff
        (r1(x2, x1))
        (...)
      )
    )
    >>> print(R(3, 3, sl.tree.struct, z)) # doctest: +ELLIPSIS
    ;; Interpret r3 as 3-step reachability
    (And
      ;; 3-step reachability from x0 to x1
      (Iff
        (r3(x0, x1))
        (Or(r2(x0, x1),
           Or(And(r2(x0, x0), r1(x0, x1)),
              And(r2(x0, x1), r1(x1, x1)),
              And(r2(x0, x2), r1(x2, x1)))))
      )
      ...
      ;; 3-step reachability from x2 to x1
      (Iff
        (r3(x2, x1))
        (Or(r2(x2, x1),
           Or(And(r2(x2, x0), r1(x0, x1)),
              And(r2(x2, x1), r1(x1, x1)),
              And(r2(x2, x2), r1(x2, x1)))))
      )
    )


    """
    assert n >= k >= 1
    sort = struct.sort
    if k == 1:
        exprs = [c.Iff(r(sort, 1)(x_i,x_j),
                       c.And(z.contains(x_i),
                             c.Not(is_stop_node(struct, x_j)),
                             S(struct, x_i, x_j)),
                       description = '1-step reachability from {} to {}'.format(x_i, x_j))
                 for x_i, x_j in itertools.product(xs(sort, n), repeat = 2)
                 if non_identical(x_i, x_j)
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
                 if non_identical(x_i, x_j)]
    cs = c.from_list(exprs)
    desc = 'Interpret {} as {}-step reachability'.format(r(sort, k), k)
    return cs.to_conjunction(description = desc)

def reach(n, struct, z):
    """
    >>> print(reach(3, sl.tree.struct, z))
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
    exprs = [R(n, k+1, struct, z) for k in range(n)]
    cs = c.from_list(exprs)
    return cs.to_conjunction(description = 'Define reachability predicates')

def defn(n, struct, z, root, *stops):
    """Define the footprint set `z` w.r.t. root node `r`.

    >>> print(defn(3, sl.tree.struct, z, sort['r']))
    ;; Define the footprint set z : SET(Int) for root r and nodes x0,...,x2
    (And
      ;; z : SET(Int) is a subset of {x0,...,x2}
      ...
      ;; If the root is a stop node, z : SET(Int) is empty
      ...
      ;; Everything in z : SET(Int) is reachable from the root r
      ...
    )


    """
    sort = struct.sort
    cs = c.ConstraintList()
    # Footprint z contains only the n allowed locations
    cs.append_expr(z.subset_of(xs_set(sort, n)),
                   description = '{} is a subset of {{{},...,{}}}'.format(z, x(sort,0), x(sort,n-1)))
    # If the root is a stop node, z is empty
    cs.append_constraint(
        c.Implies(is_stop_node(struct, root), z.is_empty(),
                  description = 'If the root is a stop node, {} is empty'.format(z))
    )
    # If the root isn't a stop node, all nodes in z are reachable from the root
    exprs = [
        c.Implies(z.contains(x_i), z3.Or(x_i == root, r(sort, n)(root, x_i)))
        for x_i in xs(sort, n)
    ]
    reach_cs = c.from_list(exprs)
    cs.append_constraint(
        reach_cs.to_conjunction(description = 'Everything in {} is reachable from the root {}'.format(z, root))
    )

    return cs.to_conjunction(description = 'Define the footprint set {} for root {} and nodes {},...,{}'.format(z, root, x(sort, 0), x(sort, n-1)))

def parents(n, struct, z):
    """parents_N: No two parents have the same child.

    >>> print(parents(3, sl.tree.struct, z)) # doctest: +ELLIPSIS
    ;; parents_N: No two parents have the same child
    (And
      ;; If a node has two identical successors they are both null
      (And
        (Implies(z[x0],
                Implies(sl.tree.left(x0) == sl.tree.right(x0),
                        sl.tree.left(x0) == sl.tree.null)))
        ...
      )
      ;; If two nodes share a successor it's null
      (And
        (Implies(And(z[x0], z[x1], Not(x0 == x1)),
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
    exprs = [z3.Implies(z.contains(x_i),
                        symbols.LAnd([
                            z3.Implies(struct.heap_fn(f)(x_i) == struct.heap_fn(g)(x_i),
                                       struct.heap_fn(f)(x_i) == struct.null)
                            for f,g in itertools.combinations(flds, 2)
                        ]))
             for x_i in xs(sort, n)]
    cs_single = c.from_list(exprs)

    def all_succs_different(x_i, x_j):
        return symbols.LAnd(
            [z3.Implies(struct.heap_fn(f)(x_i) == struct.heap_fn(g)(x_j),
                        struct.heap_fn(f)(x_i) == struct.null)
             for f,g in itertools.product(flds, repeat = 2)]
        )

    exprs2 = [
        z3.Implies(z3.And(z.contains(x_i), z.contains(x_j), z3.Not(x_i == x_j)),
                   all_succs_different(x_i, x_j))
        for x_i, x_j in itertools.combinations(xs(sort, n), 2)
    ]
    cs_double = c.from_list(exprs2)

    return c.And(
        cs_single.to_conjunction(description = 'If a node has two identical successors they are both null'),
        cs_double.to_conjunction(description = "If two nodes share a successor it's null"),
        description = 'parents_N: No two parents have the same child'
    )


def is_acyclic(n, struct, root, z):
    """The structure rooted in `root` restricted to footprint `z` is acyclic.

    >>> print(is_acyclic(3, sl.tree.struct, sort['r'], z)) # doctest: +ELLIPSIS
    ;; acyclic_N: No cycles in the structure induced by z : SET(Int)
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
    cs = c.from_list([
        parents(n, struct, z),
        c.Not(r(sort, n)(root, root),
              description = 'There is no cycle from the root to the root')
    ])
    return cs.to_conjunction(
        description = 'acyclic_N: No cycles in the structure induced by {}'.format(z)
    )

class FPVector:
    def __init__(self, **fps_by_field):
        self.fp_dict = {}
        for k,v in fps_by_field.items():
            assert isinstance(k, str)
            assert isinstance(v, generic.Set)
            self.fp_dict[k] = v

    def __getitem__(self, key):
        return self.fp_dict[key]

    def get_all(self):
        return list(self.fp_dict.values())

    def fps_for_struct(self, struct, negate_result = False):
        for fld, fp in sorted(self.fp_dict.items(),
                              key = operator.itemgetter(0)):
            if (fld in struct.fields) != negate_result:
                yield fp

    def fps_for_other_structs(self, struct):
        return self.fps_for_struct(struct, negate_result = True)

    @classmethod
    def from_dict(cls, fp_dict):
        v = cls()
        v.fp_dict = dict(fp_dict)
        return v

def is_struct_footprint(n, struct, z, y):
    """Tie `z` to the global footprint vector `y`

    >>> y = FPVector(next = fpsort['Ynext'], left = fpsort['Yleft'], right = fpsort['Yright'], data = fpsort['Ydata'])
    >>> print(is_struct_footprint(3, sl.tree.struct, z, y))
    ;; z : SET(Int) equals the global footprints for sl.tree
    (And
      ;; z : SET(Int) contains only sl.tree locations
      (Map(and, Map(and, Xdata, Xleft), Xright) ==
      Map(=>, z, Map(and, Map(and, Xdata, Xleft), Xright)))
      ;; All sl.tree footprints equal z : SET(Int)
      (And
        (z == Ydata)
        (z == Yleft)
        (z == Yright)
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
        z.subset_of(intersection),
        description = '{} contains only {} locations'.format(z, struct.name)
    )
    equal_exprs = [z.is_identical(fp) for fp in y.fps_for_struct(struct)]
    struct_equals = c.from_list(equal_exprs)
    empty_exprs = [fp.is_empty() for fp in y.fps_for_other_structs(struct)]
    other_empty = c.from_list(empty_exprs)
    combined = c.from_list([
        subset,
        struct_equals.to_conjunction(description = 'All {} footprints equal {}'.format(struct.name, z)),
        other_empty.to_conjunction(description = 'All other footprints are empty')
    ])
    return combined.to_conjunction('{} equals the global footprints for {}'.format(z, struct.name))

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

def stop_nodes_are_ordered_leaves(n, struct, z, root, *stops):
    """If there are more than two `stops`, enforce that the stop nodes
occur in the same order in the tree induced by `z` as in `stops`.

    >>> print(stop_nodes_are_ordered_leaves(3, sl.tree.struct, z, sort['root'], sort['s1'], sort['s2'])) # doctest: +ELLIPSIS
    ;; All adjacent pairs of stop nodes in (s1, s2) are ordered in the induced tree of z : SET(Int)
    (And
      ;; Stop nodes s1 and s2 have a LCA in z : SET(Int)
      (Or
        ;; x0 is the LCA of s1 and s2
        (And
          (z[x0])
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
        return c.as_constraint(True)
    else:
        sort = struct.sort

        def ordered_pair(s, t):
            exprs = [
                c.And(z.contains(x_p),
                      stops_leaf_parent(n, x_p, struct, 'left', s),
                      stops_leaf_parent(n, x_p, struct, 'right', t),
                      description = '{} is the LCA of {} and {}'.format(x_p, s, t))
                for x_p in xs(sort, n)
            ]
            return c.from_list(exprs).to_disjunction(
                description = 'Stop nodes {} and {} have a LCA in {}'.format(s, t, z)
            )

        cs_list = [
            ordered_pair(stops[k], stops[k+1])
            for k in range(len(stops)-1)
        ]

        return c.from_list(cs_list).to_conjunction(
            description = 'All adjacent pairs of stop nodes in {} are ordered in the induced tree of {}'.format(stops, z)
        )

__alpha = symbols.data_pred_var(0)
__beta = symbols.data_pred_var(1)

def unary_data_pred_holds(n, struct, z, pred):
    """Does the unary data predicate `pred` hold on `z`?

    >>> print(unary_data_pred_holds(3, sl.tree.struct, z, sl.alpha < 5))
    ;; The unary data predicate sl.alpha < 5 holds on z : SET(Int)
    (And
      (Implies(z[x0], sl.tree.data(x0) < 5))
      (Implies(z[x1], sl.tree.data(x1) < 5))
      (Implies(z[x2], sl.tree.data(x2) < 5))
    )

    """

    # TODO: Once we have fields as arrays rather than functions, we can simply map pred over the data field array -- if we convert pred into a function, that is
    sort = struct.sort
    def pred_holds_on(x_i):
        term = struct.heap_fn(struct.data_field)(x_i)
        return rewriter.partial_leaf_substitution(pred, {__alpha : term})

    cs = c.from_list([
        z3.Implies(z.contains(x_i), pred_holds_on(x_i))
        for x_i in xs(sort, n)]
    )
    return cs.to_conjunction(
        description = 'The unary data predicate {} holds on {}'.format(pred, z)
    )

def binary_data_pred_holds(n, struct, z, fld, pred):
    """Does the binary data predicate `pred` hold on `z`?

    >>> print(binary_data_pred_holds(3, sl.tree.struct, z, 'left', sl.alpha < sl.beta))
    ;; The binary data predicate sl.alpha < sl.beta holds for left descendants in z : SET(Int)
    (And
      ;; If x1 is a left-descendant of x0 then (sl.alpha < sl.beta)[sl.alpha/x0,beta/x1] holds
      (Implies(And(z[x0],
                  z[x1],
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
            z3.Implies(z3.And(z.contains(x_i),
                              z.contains(x_j),
                              z3.Or(r(sort, n)(f(x_i), x_j),
                                    f(x_i) == x_j)),
                       pred_holds_on(x_i, x_j)),
            description = 'If {x_j} is a {fld}-descendant of {x_i} then ({P})[{alpha}/{x_i},beta/{x_j}] holds'.format(x_i = x_i, x_j = x_j, P = pred, alpha = __alpha, beta = __beta, fld = fld)
        )
        for x_i,x_j in itertools.product(xs(sort, n), repeat = 2)
        if non_identical(x_i, x_j)]
    )
    return cs.to_conjunction(
        description = 'The binary data predicate {} holds for {} descendants in {}'.format(pred, fld, z)
    )

class DataPreds:
    def __init__(self, *preds):
        self.unary = []
        self.binary = {}
        for pred in preds:
            try:
                fld, pred = pred
            except TypeError:
                fld = None
            assert isinstance(pred, z3.ExprRef), \
                    'Not a data predicate: {}'.format(pred)
            if fld is None:
                self.unary.append(pred)
            else:
                self.binary.setdefault(fld, []).append(pred)

    def __iter__(self):
        yield from self.unary
        for fld, preds in self.binary.items():
            for pred in preds:
                yield fld, pred

    def __str__(self):
        return ', '.join(str(p) for p in self)

    def __repr__(self):
        return 'DataPreds({})'.format(self)

def data_preds_hold(n, struct, z, preds):
    unary = [unary_data_pred_holds(n, struct, z, pred)
             for pred in preds.unary]
    binary = [binary_data_pred_holds(n, struct, z, fld, pred)
              for fld, fld_preds in preds.binary.items()
              for pred in fld_preds]
    return c.from_list(unary + binary).to_conjunction(
        description = 'All data predicates hold')

SplitEnc = collections.namedtuple('SplitEnc', 'A B')

def struct_encoding(n, y, struct, z, preds, root, *stops):
    assert isinstance(preds, DataPreds)
    assert isinstance(y, FPVector)
    cs_a = [is_struct_footprint(n, struct, z, y),
            is_acyclic(n, struct, root, z),
            data_preds_hold(n, struct, z, preds),
            stop_nodes_are_ordered_leaves(n, struct, z, root, *stops)
    ]
    A = c.from_list(cs_a).to_conjunction('Structural encoding of list({}, {}) of size {} with data constraints {}'.format(root, stops, n, preds))
    cs_b = [reach(n, struct, z),
            defn(n, struct, z, root, *stops)
    ]
    B = c.from_list(cs_a).to_conjunction('Footprint encoding of list({}, {}) of size {}'.format(root, stops, n, preds))
    return SplitEnc(A, B)

def bounded_encoding(n, y, structs, struct, z, preds, root, *stops):
    "Top-level encoding of a formula that is a single predicate call."
    assert struct in structs
    sort = struct.sort
    A, B = struct_encoding(n, y, struct, z, preds, root, *stops)
    return c.And(
        is_bounded_heap_interpretation(n, sort, structs),
        A,
        B
    )

def z3_input(n, y, structs, struct, preds, root, *stops):
    z = struct.fp_sort['z'] # TODO: Ensure z is fresh!
    cs = bounded_encoding(n, y, structs, struct, z, preds, root, *stops)
    consts = ([root]
              + list(stops)
              + [struct.null for struct in structs]
              + [z]
              + y.get_all()
              + list(xs(struct.sort, n))
              + list(Xs(struct.sort, structs)))
    funs = itertools.chain(*(s.heap_fns() for s in structs),
                           rs(struct.sort, n))
    decls = c.SmtDecls(consts, funs)
    return c.Z3Input(cs, decls)
