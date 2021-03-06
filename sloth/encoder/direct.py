"""Direct (rather than unfolding) encoding of data structures.

.. testsetup::

   from sloth import *
   from sloth.encoder import constraints, slast
   from sloth.encoder.encoder import EncoderConfig
   from sloth.encoder.shared import FPVector
   from sloth.encoder.direct import *

"""

import itertools

import z3

from ..backend import generic, symbols
from ..utils import utils
from ..z3api import rewriter
from . import constraints as c
from . import slast
from . import shared

def is_bounded_heap_interpretation(config):
    """Delta_SL^N: Define SL* heap interpretations of size at most N

    >>> delta = is_bounded_heap_interpretation(EncoderConfig({sl.list.struct : 1, sl.tree.struct : 2}))
    >>> print(delta)
    ;; Delta_SL(3)
    (And
      ;; Global FP is the union of all field FPs
      (_X ==
      Map(or, Map(or, Map(or, _Xdata, _Xleft), _Xnext), _Xright))
      ;; Global FP is subset of {x_1,...x_n}
      (Map(=>,
          _X,
          Store(Store(Store(K(Int, False), _x0, True), _x1, True),
                _x2,
                True)) ==
      K(Int, True))
      ;; Null is not allocated
      (Not(_X[sl.list.null]))
      ;; Null is not allocated
      (Not(_X[sl.tree.null]))
      ;; Field FPs for sl.list and sl.tree don't overlap
      (K(Int, False) == Map(and, _Xnext, _Xleft))
      ;; Field FPs for sl.list and sl.tree don't overlap
      (K(Int, False) == Map(and, _Xnext, _Xright))
    )

    """
    structs = config.structs
    gs = config.global_symbols
    cs = c.ConstraintList()

    # Union constraint for all fields including data fields
    flds = sorted(set(utils.flatten(s.fields for s in structs)), key=str)
    xfs = (gs.X(fld) for fld in flds)
    cs.append_expr(gs.X().is_union_of_all(*xfs),
                   description = 'Global FP is the union of all field FPs')

    xs = gs.xs_set()
    cs.append_expr(gs.X().subset_of(xs),
                   description = 'Global FP is subset of {x_1,...x_n}')

    for s in structs:
        cs.append_expr(z3.Not(gs.X().contains(s.null)),
                       description = 'Null is not allocated')

    # Disjointness constraints only for structural fields
    for i in range(len(structs)):
        for j in range(i+1, len(structs)):
            for f in structs[i].structural_fields:
                for g in structs[j].structural_fields:
                    desc = "Field FPs for {} and {} don't overlap".format(structs[i].name, structs[j].name)
                    cs.append_expr(gs.X(f).disjoint_from(gs.X(g)),
                                   description = desc)

    return cs.to_conjunction(description = 'Delta_SL({})'.format(config.n))

def call_encoding(config, call, Y):
    "Encode the given predicate call `call` w.r.t. the footprint `Y`."
    assert config.n > 0, 'No positive size bound defined in config'
    de = DirectEncoding(config, call)
    return de.struct_encoding(Y)

class DirectEncoding:
    """
    >>> de = DirectEncoding(EncoderConfig({sl.list.struct : 2, sl.tree.struct : 1}), slast.PredCall(sl.tree.struct, 'left', sl.alpha < sl.beta, *sl.tree.locs('t u v')))
    """

    def __init__(self, config, pred_call):
        self.pred_call = pred_call
        self.n = config.n
        self.all_structs = list(sorted(config.bounds_by_struct, key=str))
        self.struct = pred_call.struct
        self.sort = self.struct.sort
        self.fp_sort = self.sort.set_sort()
        self.null = self.struct.null
        self.Z = config.get_fresh_fp()
        self._rs = config.get_fresh_reach_funs()

        # Create shorthands for accessing the global symbols
        gs = config.global_symbols
        self.x = gs.x
        self.xs = gs.xs
        self.xs_set = gs.xs_set
        self.X = gs.X
        self.Xs = gs.Xs

    def r(self, k):
        """Return the k-th reachability predicate symbol.

        >>> type(de.r(3)(de.sort['x'], de.sort['y'])).__name__
        'BoolRef'
        """
        assert 1 <= k <= self.n
        return self._rs[k-1]

    def rs(self):
        return self._rs

    def rf(self, x, y, fld):
        """Constraint that y is n-reachable from x by first taking an fld-pointer.

        >>> print(de.rf(de.x(0), de.x(1), 'left'))
        ;; _x0 is reachable from _x1 by first following field left
        (Or
          (sl.tree.left(_x0) == _x1)
          (And(_Z[sl.tree.left(_x0)], _r_3(sl.tree.left(_x0), _x1)))
        )

        """

        f = self.struct.heap_fn(fld)
        return c.Or(f(x) == y,
                     z3.And(self.Z.contains(f(x)),
                            self.r(self.n)(f(x), y)),
                    description = '{} is reachable from {} by first following field {}'.format(x,y,fld))

    def is_stop_node(self, x):
        """Return constraint that `x` is a stop node.

        `x` is a stop node if it's equal to null or any of the nodes in `stops`

        >>> print(de.is_stop_node(de.sort['x']))
        ;; x is a stop node
        (Or(x == sl.tree.null, x == u, x == v))

        """
        desc = '{} is a stop node'.format(x)
        exprs = [
            x == stop
            for stop in (self.null,*self.pred_call.stop_nodes)
        ]
        return c.as_constraint(symbols.LOr(exprs),
                               description = desc)

    def defineY(self, y):
        """Tie `_Z` to the footprint vector `y`

        >>> y = FPVector(de.fp_sort, prefix = 'Y', flds = 'next left right data'.split())
        >>> print(de.defineY(y))
        ;; defineY: _Z : SET(Int) equals the footprint parameters Y for sl.tree
        (And
          ;; All sl.tree footprints equal _Z : SET(Int)
          (And
            (_Z == Ydata)
            (_Z == Yleft)
            (_Z == Yright)
          )
          ;; All other footprints are empty
          (And
            (Ynext == K(Int, False))
          )
        )

        """
        assert isinstance(y, shared.FPVector), utils.wrong_type(y)
        struct = self.struct
        Z = self.Z
        equal_exprs = (Z.is_identical(fp) for fp in y.fps_for_struct(struct))
        ls = [
            c.And(*equal_exprs, description = 'All {} footprints equal {}'.format(struct.name, Z))
        ]
        empty_exprs = [fp.is_empty() for fp in y.fps_for_other_structs(struct)]
        if empty_exprs:
            ls.append(c.And(
                *empty_exprs,
                description = 'All other footprints are empty')
            )

        return c.And(*ls, description = 'defineY: {} equals the footprint parameters {} for {}'.format(Z, y, struct.name))

    def S(self, x, y):
        """Successor relation for `x` and `y`.

        >>> print(de.S(de.sort['x'], de.sort['y']))
        ;; y is a ['left', 'right']-successor of x
        (Or
          (sl.tree.left(x) == y)
          (sl.tree.right(x) == y)
        )

        """
        struct = self.struct
        flds = struct.structural_fields
        exprs = [struct.heap_fn(fld)(x) == y for fld in flds]
        desc = '{} is a {}-successor of {}'.format(y, flds, x)
        return c.Or(*exprs, description = desc)

    def R(self, k):
        """Define r_k as the k-step reachability relation within the footprint z.

        >>> print(de.R(1)) # doctest: +ELLIPSIS
        ;; Interpret _r_1 as 1-step reachability
        (And
          ;; 1-step reachability from _x0 to _x0
          ...
          ;; 1-step reachability from _x0 to _x1
          (Iff
            (_r_1(_x0, _x1))
            (And
              (_Z[_x0])
              (Not
                ;; _x1 is a stop node
                (Or(_x1 == sl.tree.null, _x1 == u, _x1 == v))
              )
              ;; _x1 is a ['left', 'right']-successor of _x0
              (Or
                (sl.tree.left(_x0) == _x1)
                (sl.tree.right(_x0) == _x1)
              )
            )
          )
          ...
          ;; 1-step reachability from _x2 to _x2
          (Iff
            (_r_1(_x2, _x2))
            (...)
          )
        )
        >>> print(de.R(3)) # doctest: +ELLIPSIS
        ;; Interpret _r_3 as 3-step reachability
        (And
          ;; 3-step reachability from _x0 to _x0
          ...
          ;; 3-step reachability from _x0 to _x1
          (Iff
            (_r_3(_x0, _x1))
            (Or(_r_2(_x0, _x1),
               Or(And(_r_2(_x0, _x0), _r_1(_x0, _x1)),
                  And(_r_2(_x0, _x1), _r_1(_x1, _x1)),
                  And(_r_2(_x0, _x2), _r_1(_x2, _x1)))))
          )
          ...
          ;; 3-step reachability from _x2 to _x2
          (Iff
            (_r_3(_x2, _x2))
            (Or(_r_2(_x2, _x2),
               Or(And(_r_2(_x2, _x0), _r_1(_x0, _x2)),
                  And(_r_2(_x2, _x1), _r_1(_x1, _x2)),
                  And(_r_2(_x2, _x2), _r_1(_x2, _x2)))))
          )
        )


        """
        assert self.n >= k >= 1
        struct = self.struct
        Z = self.Z
        stops = self.pred_call.stop_nodes

        if k == 1:
            exprs = (c.Iff(self.r(1)(x_i,x_j),
                           c.And(Z.contains(x_i),
                                 c.Not(self.is_stop_node(x_j)),
                                 self.S(x_i, x_j)),
                           description = '1-step reachability from {} to {}'.format(x_i, x_j))
                     for x_i, x_j in itertools.product(self.xs(), repeat = 2)
                     # Note: To be able to check acyclicity, we have to compute reachability even for x_i=x_j
                     #if non_identical(x_i, x_j)
            )
        else:
            def step(x_i, x_j):
                exprs = [z3.And(self.r(k-1)(x_i, x_k), self.r(1)(x_k, x_j))
                         for x_k in self.xs()]
                return symbols.LOr(exprs)

            exprs = (c.Iff(self.r(k)(x_i,x_j),
                           z3.Or(self.r(k - 1)(x_i,x_j),
                                 step(x_i, x_j)),
                           description = '{}-step reachability from {} to {}'.format(k, x_i, x_j))
                     for x_i, x_j in itertools.product(self.xs(), repeat = 2)
                     # Note: To be able to check acyclicity, we have to compute reachability even for x_i=x_j
                     #if non_identical(x_i, x_j)
            )
        return c.And(
            *exprs,
            description = 'Interpret {} as {}-step reachability'.format(self.r(k), k)
        )

    def reach(self):
        """
        >>> print(de.reach())
        ;; Define reachability predicates
        (And
          ;; Interpret _r_1 as 1-step reachability
          ...
          ;; Interpret _r_2 as 2-step reachability
          ...
          ;; Interpret _r_3 as 3-step reachability
          ...
        )

        """
        exprs = (self.R(k+1) for k in range(self.n))
        return c.And(*exprs, description = 'Define reachability predicates')

    def emptyZ(self):
        """Formalize under which circumstances Z must be empty.

        >>> print(de.emptyZ())
        ;; The root is such that _Z : SET(Int) must be empty
        (Or
          ;; t is a stop node
          (Or(t == sl.tree.null, t == u, t == v))
          (And(Not(_x0 == t), Not(_x1 == t), Not(_x2 == t)))
        )

        """
        root = self.pred_call.root
        return c.Or(
            self.is_stop_node(root),
            z3.And([z3.Not(x_i == root) for x_i in self.xs()]),
            description = 'The root is such that {} must be empty'.format(self.Z)
        )

    def footprint(self):
        """Define the footprint set `Z` as what's reachble from the root node.

        >>> print(de.footprint())
        ;; footprint: Define the set _Z : SET(Int) for root t and nodes _x0,...,_x2
        (And
          ;; _Z : SET(Int) is a subset of {_x0,...,_x2}
          (Map(=>,
              _Z,
              Store(Store(Store(K(Int, False), _x0, True), _x1, True),
                    _x2,
                    True)) ==
          K(Int, True))
          ;; Define when _Z : SET(Int) is empty
          (Implies
            ;; The root is such that _Z : SET(Int) must be empty
            ...
            (_Z == K(Int, False))
          )
          ;; If the root is allocated, _Z : SET(Int) contains exactly what's reachable from the root
          (Implies
            (Not
              ;; The root is such that _Z : SET(Int) must be empty
              ...
            )
            ;; Everything in _Z : SET(Int) is reachable from the root t
            (And
              (Iff
                (_Z[_x0])
                (Or(t == _x0, _r_3(t, _x0)))
              )
              ...
              (Iff
                (_Z[_x2])
                (Or(t == _x2, _r_3(t, _x2)))
              )
            )
          )
        )

        """
        n = self.n
        struct = self.struct
        Z = self.Z
        root = self.pred_call.root
        stops = self.pred_call.stop_nodes
        cs = c.ConstraintList()
        # Footprint Z contains only the n allowed locations
        cs.append_expr(Z.subset_of(self.xs_set()),
                       description = '{} is a subset of {{{},...,{}}}'.format(Z, self.x(0), self.x(n - 1)))
        # If the root is a stop node or outside x_1...x_n, Z is empty
        cs.append_constraint(
            c.Implies(self.emptyZ(), Z.is_empty(),
                      description = 'Define when {} is empty'.format(Z))
        )

        # Define Z for nonempty footprints
        exprs = (
            c.Iff(
                Z.contains(x_i),
                z3.Or(root == x_i,
                      self.r(n)(root, x_i))
            )
            for x_i in self.xs()
        )

        cs.append_constraint(
            c.Implies(c.Not(self.emptyZ()),
                      c.And(*exprs,
                            description = 'Everything in {} is reachable from the root {}'.format(Z, root)),
                      description = "If the root is allocated, {} contains exactly what's reachable from the root".format(Z)))


        return cs.to_conjunction(description = 'footprint: Define the set {} for root {} and nodes {},...,{}'.format(Z, root, self.x(0), self.x(n-1)))

    def oneparent(self):
        """Every non-null nodes has at most one incoming pointer.

        >>> print(de.oneparent()) # doctest: +ELLIPSIS
        ;; oneparent: Every non-null nodes has at most one incoming pointer
        (And
          ;; If a node has two identical successors they are both null
          (And
            (Implies(_Z[_x0],
                    Implies(sl.tree.left(_x0) == sl.tree.right(_x0),
                            sl.tree.left(_x0) == sl.tree.null)))
            ...
          )
          ;; If two nodes share a successor it's null
          (And
            (Implies(And(_Z[_x0], _Z[_x1], Not(_x0 == _x1)),
                    And(Implies(sl.tree.left(_x0) == sl.tree.left(_x1),
                                sl.tree.left(_x0) == sl.tree.null),
                        Implies(sl.tree.left(_x0) == sl.tree.right(_x1),
                                sl.tree.left(_x0) == sl.tree.null),
                        Implies(sl.tree.right(_x0) == sl.tree.left(_x1),
                                sl.tree.right(_x0) == sl.tree.null),
                        Implies(sl.tree.right(_x0) == sl.tree.right(_x1),
                                sl.tree.right(_x0) == sl.tree.null))))
            ...
          )
        )

        """
        struct = self.struct
        Z = self.Z
        flds = struct.structural_fields

        ls = []

        if not struct.is_linear():
            # Ensure that if a node has the same successor twice, they are both null
            # This only makes sense for branching structures
            exprs = (z3.Implies(Z.contains(x_i),
                                symbols.LAnd([
                                    z3.Implies(struct.heap_fn(f)(x_i) == struct.heap_fn(g)(x_i),
                                               struct.heap_fn(f)(x_i) == struct.null)
                                    for f,g in itertools.combinations(flds, 2)
                                ]))
                     for x_i in self.xs())
            ls.append(c.And(
                *exprs,
                description = 'If a node has two identical successors they are both null'
            ))

        def all_succs_different(x_i, x_j):
            return symbols.LAnd(
                [z3.Implies(struct.heap_fn(f)(x_i) == struct.heap_fn(g)(x_j),
                            struct.heap_fn(f)(x_i) == struct.null)
                 for f,g in itertools.product(flds, repeat = 2)]
            )

        if self.n > 1:
            exprs2 = (
                z3.Implies(z3.And(Z.contains(x_i), Z.contains(x_j), z3.Not(x_i == x_j)),
                           all_succs_different(x_i, x_j))
                for x_i, x_j in itertools.combinations(self.xs(), 2)
            )
            ls.append(c.And(
                *exprs2,
                description = "If two nodes share a successor it's null"
            ))

        return c.And(
            *ls,
            description = 'oneparent: Every non-null nodes has at most one incoming pointer'
        )


    def structure(self):
        """The structure rooted in `root` restricted to footprint `Z` is acyclic.

        >>> print(de.structure()) # doctest: +ELLIPSIS
        ;; structure: _Z : SET(Int) is an acyclic data structure rooted in t
        (And
          ;; The root is in _Z : SET(Int)
          (Implies
            (Not
              ;; t is a stop node
              (Or(t == sl.tree.null, t == u, t == v))
            )
            (_Z[t])
          )
          ;; oneparent: Every non-null nodes has at most one incoming pointer
          ...
          ;; There is no cycle from the root to the root
          (Not
            (_r_3(t, t))
          )
        )

        """
        n = self.n
        root = self.pred_call.root
        Z = self.Z
        return c.And(
            c.Implies(c.Not(self.is_stop_node(root)), Z.contains(root), description = 'The root is in {}'.format(Z)),
            self.oneparent(),
            c.Not(self.r(n)(root, root), description = 'There is no cycle from the root to the root'),
            description = 'structure: {} is an acyclic data structure rooted in {}'.format(Z, root)
        )

    def all_leaves_are_stop_nodes(self):
        Z = self.Z
        struct = self.struct
        stops = self.pred_call.stop_nodes
        fld_fns = [(fld, struct.heap_fn(fld)) for fld in struct.structural_fields]
        exprs = (c.Implies(
            z3.And(Z.contains(x_i), z3.Not(Z.contains(fld_fn(x_i)))),
            self.is_stop_node(fld_fn(x_i)),
            description = "If the {}-successor of {} isn't alloced it's a stop node".format(fld, x_i))
                 for x_i in self.xs()
                 for fld, fld_fn in fld_fns)
        return c.And(*exprs, description = 'All leaves are stop nodes')

    def stop_reachable_by_fld(self, x_p, fld, stop):
        """`x_p` is a `fld`-ancestor of `stop`.

        >>> print(de.stop_reachable_by_fld(de.sort['x_p'], 'right', de.sort['x_stop']))
        ;; fstop: x_p is a right-ancestor of the stop node x_stop
        (Or
          (sl.tree.right(x_p) == x_stop)
          ;; A right-descendant of x_p is the parent of the stop node x_stop
          (Or
            ;; _x0 is the descendant that is the parent of x_stop
            (And
              ;; x_p is reachable from _x0 by first following field right
              (Or
                (sl.tree.right(x_p) == _x0)
                (And(_Z[sl.tree.right(x_p)], _r_3(sl.tree.right(x_p), _x0)))
              )
              (_Z[_x0])
              ;; x_stop is a ['left', 'right']-successor of _x0
              (Or
                (sl.tree.left(_x0) == x_stop)
                (sl.tree.right(_x0) == x_stop)
              )
            )
            ;; _x1 is the descendant that is the parent of x_stop
            ...
            ;; _x2 is the descendant that is the parent of x_stop
            ...
          )
        )

        """
        struct = self.struct
        Z = self.Z
        assert struct.unqualified_name == 'tree', \
            'Redundant stop point constraint for non-tree structure'

        exprs = (
            c.And(
                self.rf(x_p, x_c, fld),
                Z.contains(x_c),
                self.S(x_c, stop),
                description = '{} is the descendant that is the parent of {}'.format(x_c, stop)
            )
            for x_c in self.xs()
        )
        descendant_constraint = c.Or(
            *exprs,
            description = 'A {}-descendant of {} is the parent of the stop node {}'.format(fld, x_p, stop)
        )

        return c.Or(
            struct.heap_fn(fld)(x_p) == stop,
            descendant_constraint,
            description = 'fstop: {} is a {}-ancestor of the stop node {}'.format(x_p, fld, stop)
        )

    def stop_nodes_are_ordered_leaves(self):
        """If there are more than two `stops`, enforce that the stop nodes
    occur in the same order in the tree induced by `Z` as in `stops`.

        >>> print(de.stop_nodes_are_ordered_leaves()) # doctest: +ELLIPSIS
        ;; ordered: All adjacent pairs of stop nodes in [u, v] are ordered in the induced tree of _Z : SET(Int)
        (And
          ;; Stop nodes u and v have an LCA in _Z : SET(Int)
          (Or
            ;; _x0 is the LCA of u and v
            (And
              (_Z[_x0])
              ;; fstop: _x0 is a left-ancestor of the stop node u
              ...
              ;; fstop: _x0 is a right-ancestor of the stop node v
              ...
            )
            ;; _x1 is the LCA of u and v
            (And
              (_Z[_x1])
              ;; fstop: _x1 is a left-ancestor of the stop node u
              ...
              ;; fstop: _x1 is a right-ancestor of the stop node v
              ...
            )
            ;; _x2 is the LCA of u and v
            ...
          )
        )

        """
        struct = self.struct
        Z = self.Z
        root = self.pred_call.root
        stops = self.pred_call.stop_nodes
        if len(stops) <= 1:
            msg = 'Stop-node order constraints can only be generated for >= 2 stop nodes, but got {}'
            raise utils.SlothException(msg.format(len(stops)))
        else:
            def ordered_pair(s, t):
                exprs = (
                    c.And(Z.contains(x_p),
                          self.stop_reachable_by_fld(x_p, 'left', s),
                          self.stop_reachable_by_fld(x_p, 'right', t),
                          description = '{} is the LCA of {} and {}'.format(x_p, s, t))
                    for x_p in self.xs()
                )
                return c.Or(
                    *exprs,
                    description = 'Stop nodes {} and {} have an LCA in {}'.format(s, t, Z)
                )

            ordered = [
                ordered_pair(stops[k], stops[k+1])
                for k in range(len(stops)-1)
            ]

            return c.And(*ordered,
                         description = 'ordered: All adjacent pairs of stop nodes in {} are ordered in the induced tree of {}'.format(stops, Z)
            )

    def stops_distinct(self):
        """The stops nodes are distinct.

        >>> print(de.stops_distinct())
        ;; Stop nodes are pairwise different
        (And
          (Not(u == v))
        )

        """
        stops = self.pred_call.stop_nodes
        if len(stops) > 1:
            exprs = (z3.Not(s == t) for s, t in itertools.combinations(stops, 2))
        else:
            exprs = (symbols.Z3True,)
        return c.And(*exprs,
                     description = 'Stop nodes are pairwise different')

    def stops_occur(self):
        """All stop nodes occur.

        >>> print(de.stops_occur())
        ;; All stop nodes occur
        (And
          ;; If the tree is non-empty, it contains the node u
          (Or
            ;; _x0 is alloced and one of its descendants is node u
            (And
              (_Z[_x0])
              ;; u is a ['left', 'right']-successor of _x0
              (Or
                (sl.tree.left(_x0) == u)
                (sl.tree.right(_x0) == u)
              )
            )
            ;; _x1 is alloced and one of its descendants is node u
            (And
              (_Z[_x1])
              ;; u is a ['left', 'right']-successor of _x1
              (Or
                (sl.tree.left(_x1) == u)
                (sl.tree.right(_x1) == u)
              )
            )
            ;; _x2 is alloced and one of its descendants is node u
            (And
              (_Z[_x2])
              ;; u is a ['left', 'right']-successor of _x2
              (Or
                (sl.tree.left(_x2) == u)
                (sl.tree.right(_x2) == u)
              )
            )
          )
          ;; If the tree is non-empty, it contains the node v
          (Or
            ;; _x0 is alloced and one of its descendants is node v
            (And
              (_Z[_x0])
              ;; v is a ['left', 'right']-successor of _x0
              (Or
                (sl.tree.left(_x0) == v)
                (sl.tree.right(_x0) == v)
              )
            )
            ;; _x1 is alloced and one of its descendants is node v
            (And
              (_Z[_x1])
              ;; v is a ['left', 'right']-successor of _x1
              (Or
                (sl.tree.left(_x1) == v)
                (sl.tree.right(_x1) == v)
              )
            )
            ;; _x2 is alloced and one of its descendants is node v
            (And
              (_Z[_x2])
              ;; v is a ['left', 'right']-successor of _x2
              (Or
                (sl.tree.left(_x2) == v)
                (sl.tree.right(_x2) == v)
              )
            )
          )
        )


        """
        struct = self.struct
        Z = self.Z

        def stop_occurs(node):
            return c.Or(
                *(c.And(Z.contains(x_i),
                        self.S(x_i, node),
                        description = '{} is alloced and one of its descendants is node {}'.format(x_i, node))
                  for x_i in self.xs()),
                description = 'If the {} is non-empty, it contains the node {}'.format(struct.unqualified_name, node)
        )

        exprs = (stop_occurs(s) for s in self.pred_call.stop_nodes)
        return c.And(*exprs, description = 'All stop nodes occur')

    def stop_constraints(self):
        """The conjunct of all stop-node constraints.

        >>> print(de.stop_constraints())
        ;; stops^sl.tree: Combined stop node constraints
        (And
          ;; Stop nodes are pairwise different
          ...
          ;; If the root is a stop node, it's equal to all stop nodes
          (Implies
            ;; t is a stop node
            (Or(t == sl.tree.null, t == u, t == v))
            (And(t == u, t == v))
          )
          ;; If the root isn't a stop node then all stop nodes occur
          (Implies
            (Not
              ;; t is a stop node
              (Or(t == sl.tree.null, t == u, t == v))
            )
            ;; All stop nodes occur
            ...
          )
          ;; All leaves are stop nodes
          ...
          ;; ordered: All adjacent pairs of stop nodes in [u, v] are ordered in the induced tree of _Z : SET(Int)
          ...
        )


        """

        call = self.pred_call
        root = call.root
        stops = call.stop_nodes
        exprs = [
            self.stops_distinct(),
            c.Implies(self.is_stop_node(root),
                      c.And(*[root == s for s in stops]),
                      description = "If the root is a stop node, it's equal to all stop nodes"),
            c.Implies(c.Not(self.is_stop_node(root)), self.stops_occur(),
                      description = "If the root isn't a stop node then all stop nodes occur"),
            self.all_leaves_are_stop_nodes()
        ]
        if len(stops) > 1:
            exprs.append(self.stop_nodes_are_ordered_leaves())
        return c.And(*exprs, description = 'stops^{}: Combined stop node constraints'.format(self.struct))

    __alpha = symbols.data_pred_var(0)
    __beta = symbols.data_pred_var(1)

    def unary_data_pred_holds(self, pred):
        """Does the unary data predicate `pred` hold on `Z`?

        >>> print(de.unary_data_pred_holds(sl.alpha < 5))
        ;; The unary data predicate sl.alpha < 5 holds on _Z : SET(Int)
        (And
          (Implies(_Z[_x0], sl.tree.data(_x0) < 5))
          (Implies(_Z[_x1], sl.tree.data(_x1) < 5))
          (Implies(_Z[_x2], sl.tree.data(_x2) < 5))
        )

        """

        # TODO: Once we have fields as arrays rather than functions, we can simply map pred over the data field array -- if we convert pred into a function, that is
        struct = self.struct
        Z = self.Z
        def pred_holds_on(x_i):
            term = struct.heap_fn(struct.data_field)(x_i)
            return rewriter.partial_leaf_substitution(pred, {self.__alpha : term})

        exprs = [
            z3.Implies(Z.contains(x_i), pred_holds_on(x_i))
            for x_i in self.xs()
        ]
        return c.And(*exprs,
                     description = 'The unary data predicate {} holds on {}'.format(pred, Z))

    def binary_data_pred_holds(self, fld, pred):
        """Does the binary data predicate `pred` hold on `Z`?

        >>> print(de.binary_data_pred_holds('left', sl.alpha < sl.beta))
        ;; The binary data predicate sl.alpha < sl.beta holds for left descendants in _Z : SET(Int)
        (And
          (Implies
            (And
              (_Z[_x0])
              (_Z[_x1])
              ;; _x0 is reachable from _x1 by first following field left
              (Or
                (sl.tree.left(_x0) == _x1)
                (And(_Z[sl.tree.left(_x0)], _r_3(sl.tree.left(_x0), _x1)))
              )
            )
            (sl.tree.data(_x0) < sl.tree.data(_x1))
          )
          ...
        )

        """
        struct = self.struct
        Z = self.Z
        def pred_holds_on(x_i, x_j):
            term = struct.heap_fn(struct.data_field)(x_i)
            term2 = struct.heap_fn(struct.data_field)(x_j)
            return rewriter.partial_leaf_substitution(pred, {self.__alpha : term,
                                                             self.__beta : term2})

        exprs = (
            c.as_constraint(
                c.Implies(c.And(Z.contains(x_i),
                                Z.contains(x_j),
                                self.rf(x_i, x_j, fld)),
                           pred_holds_on(x_i, x_j)),
                description = 'If {x_j} is a {fld}-descendant of {x_i} then ({P})[{alpha}/{x_i},beta/{x_j}] holds'.format(x_i = x_i, x_j = x_j, P = pred, alpha = self.__alpha, beta = self.__beta, fld = fld)
            )
            for x_i,x_j in itertools.product(self.xs(), repeat = 2)
            if non_identical(x_i, x_j)
        )
        return c.And(*exprs,
                     description = 'The binary data predicate {} holds for {} descendants in {}'.format(pred, fld, Z))

    def data_preds_hold(self, preds):
        # TODO: The possibility to associate multiple predicates with a single call is currently unused, but it's conceivable we use it in the future, based on some AST rewriting that groups pred calls together or something like that
        unary = (self.unary_data_pred_holds(pred)
                 for pred in preds.unary)
        binary = (self.binary_data_pred_holds(fld, pred)
                  for fld, fld_preds in preds.binary.items()
                  for pred in fld_preds)
        return c.And(*unary, *binary, description = 'All data predicates hold')

    def is_well_typed(self):
        struct = self.struct
        root = self.pred_call.root
        stops = self.pred_call.stop_nodes
        other_structs = [s for s in self.all_structs if s is not struct]
        exprs = [z3.Not(self.X(fld).contains(v))
                 for os in other_structs
                 for fld in os.structural_fields
                 for v in (root, *stops)]
        return c.And(*exprs,
                     description = "The root {} and stop points {} aren't allocated in other structs".format(root, stops))

    def no_loop_on_null_node(self):
        root = self.pred_call.root
        return c.as_constraint(
            z3.Not(self.r(self.n)(self.null, self.null)),
            description = "Null can't be reachable from itself"
        )

    # def no_loop_on_root_node(self):
    #     root = self.pred_call.root
    #     return c.as_constraint(
    #         z3.Not(self.r(self.n)(root, root)),
    #         description = "The root {} can't be reachable from itself".format(self.pred_call.root)
    #     )

    # def no_loop_on_stop_node(self):
    #     root = self.pred_call.root
    #     return c.Implies(
    #         self.is_stop_node(root),
    #         z3.Not(self.r(self.n)(root, root)),
    #         description = "If {} is a stop node, it can't be reachable from itself".format(self.pred_call.root)
    #     )

    def struct_encoding(self, Y):
        assert isinstance(Y, shared.FPVector), utils.wrong_type(Y)
        struct = self.struct
        Z = self.Z
        call = self.pred_call
        root = call.root
        stops = call.stop_nodes
        if call.pred is not None:
            preds = shared.DataPreds((call.fld, call.pred))
        else:
            preds = None
        cs_a = [self.structure(),
                self.is_well_typed(),
                self.stop_constraints()
        ]
        if preds is not None:
            cs_a.append(self.data_preds_hold(preds))
        A = c.And(
            *cs_a,
            description = 'Structural encoding of list({}, {}) of size {} with data constraints {}'.format(root, stops, self.n, preds)
        )
        cs_b = [self.reach(),
                self.footprint(),
                self.defineY(Y),
                self.no_loop_on_null_node()
                #self.no_loop_on_stop_node()
        ]
        B = c.And(
            *cs_b, description = 'Footprint encoding of list({}, {}) of size {}'.format(root, stops, self.n, preds)
        )
        fresh_decls = set(itertools.chain([Z],
                                          self.xs(),
                                          self.rs()))
        return shared.SplitEnc(A, B, fresh_decls)

###############################################################################
# Static utilities
###############################################################################

def non_identical(x_i, x_j):
    # For some reason x_i is not x_j doesn't appear to do the right thing
    return str(x_i) != str(x_j)
