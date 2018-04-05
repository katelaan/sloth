"""Direct (rather than unfolding) encoding of data structures.

.. testsetup::

   from sloth import *
   from sloth.encoder import constraints
   from sloth.encoder.direct import *
   sort = LambdaBackend.make_loc_sort(None)

"""

import itertools

import z3

from . import constraints as c
from ..backend import LambdaBackend, generic, lambdas, symbols
from ..utils import utils

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

def X(sort, fld = None):
    """Return the global FP variable for the given field.

    If no field is given, return the variable for the union.
    """
    assert(isinstance(sort, generic.SlSort))
    suffix = fld if fld is not None else ''
    return sort.set_sort()['X' + suffix]

def r(sort, k):
    return z3.Function('r{}'.format(k), sort.ref, sort.ref, z3.BoolSort())

def delta_sl(n, sort, structs):
    """Define SL* heap interpretations of size at most N

    >>> delta = delta_sl(3, LambdaBackend.make_loc_sort(None), [sl.list.struct, sl.tree.struct])
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

    xs = lambdas.LambdaSet.to_set(sort, *(x(sort, i) for i in range(n)))
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

def S(struct, flds, x, y):
    """Successor relation for `x` and `y` w.r.t. `flds`.

    >>> print(S(sl.tree.struct, ['left','right'], sort['x'], sort['y']))
    ;; y is a ['left', 'right']-successor of x
    (Or
      (And(Xleft[x], sl.tree.left(x) == y))
      (And(Xright[x], sl.tree.right(x) == y))
    )


    """
    exprs = [z3.And(X(struct.sort, fld).contains(x),
                    struct.heap_fn(fld)(x) == y)
             for fld in flds]
    cs = c.ConstraintList.from_list(exprs)
    desc = '{} is a {}-successor of {}'.format(y, flds, x)
    return cs.to_disjunction(description = desc)

# def S(struct, flds, x, y):
#     """Successor relation for `x` and `y` w.r.t. `flds`.

#     >>> print(S(sl.tree.struct, ['left','right'], x(sort, 0), x(sort, 1)))
#     Or(And(Xleft[x0], sl.tree.left(x0) == x1),
#        And(Xright[x0], sl.tree.right(x0) == x1))

#     """
#     exprs = [z3.And(X(struct.sort, fld).contains(x),
#                     struct.heap_fn(fld)(x) == y)
#              for fld in flds]
#     return symbols.LOr(exprs)

def R(n, k, struct, flds, z):
    """Define r_k as the k-step reachability relation within the footprint z.

    >>> z = sl.tree.struct.fp_sort['z']
    >>> print(R(3, 1, sl.tree.struct, ['left','right'], z)) # doctest: +ELLIPSIS
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
    >>> print(R(3, 3, sl.tree.struct, ['left','right'], z)) # doctest: +ELLIPSIS
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
    sort = struct.sort
    if k == 1:
        # exprs = [r(sort, 1)(x_i,x_j) == z3.And(z.contains(x_i),
        #                               z3.Not(is_stop_node(struct, x_j).to_z3_expr()),
        #                               S(struct, flds, x_i, x_j))
        #          for x_i, x_j in itertools.product(xs(sort, n), repeat = 2)
        #          if str(x_i) != str(x_j)
        # ]
        exprs = [c.Iff(r(sort, 1)(x_i,x_j),
                       c.And(z.contains(x_i),
                             c.Not(is_stop_node(struct, x_j)),
                             S(struct, flds, x_i, x_j)),
                       description = '1-step reachability from {} to {}'.format(x_i, x_j))
                 for x_i, x_j in itertools.product(xs(sort, n), repeat = 2)
                 if str(x_i) != str(x_j)
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
                 if str(x_i) != str(x_j)]
    cs = c.ConstraintList.from_list(exprs)
    desc = 'Interpret {} as {}-step reachability'.format(r(sort, k), k)
    return cs.to_conjunction(description = desc)

def reach(n, flds, z):
    cs = c.ConstraintList()

def defn(n, z, x, *stops):
    pass

def parents(n, flds, z):
    pass

def is_acyclic(n, flds, z):
    pass

def is_list(n, z):
    pass

def is_tree(n, z):
    pass

def stops_leaf_parent(x_p, f, *stops):
    pass

def stop_nodes_are_ordered_leaves():
    pass

def unary_data_pred_holds(z, pred):
    pass

def binary_data_pred_holds(z, fld, pred):
    pass

def data_preds_hold(z, preds):
    pass
