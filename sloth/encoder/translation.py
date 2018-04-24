"""Encoding of non-call SL formulas.

The logic for encoding calls is injected via an
:class:`encoder.EncoderConfig` object, as is the generation of global
constraints (e.g. the Delta formula from the IJCAR paper.)

.. testsetup::

   import functools
   import z3
   from sloth import *
   from sloth.slbuilders import *
   from sloth.model.graph import Graph, print_all_named_ptrs
   from sloth.encoder.translation import *

>>> eval_ = evaluate_to_graph
>>> x, y, z = sl.list.locs('x y z'); t, u, v, w = sl.tree.locs('t u v w'); d, e, f = z3.Ints('d e f')

Note that for some inputs that don't explicitly reference null, it
cannot be predicted whether z3 includes null in the model. In such
cases, we pass the `ignore_null` flag to the evaluation function to
suppress including null nodes in the graph model. This way we don't
care whether null is in z3's model or not.

For some other benchmarks, such as `sl.list(x)`, z3's output is also
nondeterministic. In such cases we check that the solution we get is
among the solutions that z3 returns.

If a test case fails, you should check whether the output is in fact
also valid but not among the ones tested for. If so, we check against
a set of valid solutions with the following auxiliary function:

>>> def is_in(g, gs): return (True if g in gs else g)

Single pointers and small separating conjunctions of pointers / equalities
--------------------------------------------------------------------------

>>> is_sat(sl.list.pointsto(x, y))
True
>>> eval_(sl.list.pointsto(x, y))
Graph({0, 1, 2}, {(1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2})
>>> eval_(sl.tree.pointsto(t, u, v))
Graph({0, 1, 2, 3}, {(1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3})
>>> eval_(sl.tree.left(t,u))
Graph({0, 1, 2}, {(1, 'left'): 2}, {'sl.tree.null': 0, 't': 1, 'u': 2})
>>> eval_(sl.sepcon(sl.tree.left(t,u), sl.tree.right(t,v)))
Graph({0, 1, 2, 3}, {(1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3})
>>> eval_(sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z)))
Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})
>>> eval_(sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null)))
Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})
>>> eval_(sl.list.eq(x,y))
Graph({0}, {}, {'x': 0, 'y': 0})
>>> eval_(sl.sepcon(sl.list.pointsto(x, y), sl.list.eq(x, y)))
Graph({0, 1}, {(1, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 1})

Mixing data structures in one expression:

>>> eval_(sl.sepcon(sl.list.pointsto(x,y), sl.tree.pointsto(t,u,v)), ignore_null = True)
Graph({0, 1, 2, 3, 4}, {(0, 'left'): 1, (0, 'right'): 2, (3, 'next'): 4}, {'t': 0, 'u': 1, 'v': 2, 'x': 3, 'y': 4})

Input with Boolean structure
----------------------------

>>> eval_(z3.And(sl.list.pointsto(x,y), sl.list.pointsto(z, y)))
Graph({0, 1, 2}, {(1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 1})
>>> eval_(z3.And(sl.list.pointsto(x,y), sl.list.pointsto(x, sl.list.null)))
Graph({0, 1}, {(1, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 0})

For the following disjunction, z3 sometimes returns a tree model and
sometimes returns a list model. (Because there is allocation in only
one of structures, it's fine that z3 interprets x and t as the same
value in the list case.)

>>> is_in(eval_(z3.Or(sl.list.pointsto(x,y), sl.tree.pointsto(t, u, v)), ignore_null = True), (Graph({0, 1, 2, 3}, {(0, 'left'): 1, (0, 'right'): 2}, {'t': 0, 'u': 1, 'v': 2, 'x': 3}), Graph({0, 1}, {(0, 'next'): 1}, {'t': 0, 'x': 0, 'y': 1})))
True
>>> eval_(z3.Not(sl.list.pointsto(x,y)), ignore_null = True)
Graph({0}, {}, {'x': 0})
>>> eval_(z3.And(sl.list.pointsto(y,x), z3.Not(sl.list.pointsto(x,y))))
Graph({0, 1, 2}, {(2, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 2})
>>> eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, z)), sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, x))))
Graph({0, 1, 2}, {(1, 'next'): 2, (2, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 1})
>>> eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, z)), z3.Not(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(y, x)))))
Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})

Simple unsatisfiable benchmarks
-------------------------------

>>> is_sat(sl.sepcon(sl.list.pointsto(x,y), sl.list.pointsto(x,y)))
False
>>> is_sat(z3.And(sl.list.pointsto(x, y), z3.Not(sl.list.pointsto(x,y))))
False
>>> is_sat(z3.And(sl.sepcon(sl.list.pointsto(x, y), sl.list.eq(x, z)), z3.Not(sl.list.pointsto(z, y))))
False

Benchmarks with data constraints
--------------------------------

In the following test cases, there is sometimes more than one choice
for satisfying the data constraints. The current version of z3 gives a
deterministic output for these, so checking for graph isomorphism is
still fine. But with other versions of z3, some test cases might
actually break even though the code is correct. (Larger values than 43
and 9000 for the third and fourth benchmark below.)

>>> eval_(sl.sepcon(sl.list.data(x,d), d == 42))
Graph({0, 1}, {(1, 'data'): 42}, {'sl.list.null': 0, 'x': 1}, {'d': 42})
>>> eval_(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d == 42))
Graph({0, 1, 2}, {(1, 'data'): 42, (1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 42})
>>> eval_(z3.And(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d > 42), sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d < 9000)))
Graph({0, 1, 2}, {(1, 'data'): 43, (1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 43})
>>> eval_(z3.And(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d > 42), z3.Not(sl.sepcon(sl.list.data(x,d), sl.list.next(x,y), d < 9000))))
Graph({0, 1, 2}, {(1, 'data'): 9000, (1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 9000})

Benchmarks with list calls
--------------------------

Note that in many of the remaining examples, data values are
underconstrained. For this reason, we don't require exact data values
in the graph output, but we check with separate API calls that the
data interpretation is consistent with the constraints that are there.

>>> is_in(eval_(sl.list(x)), (Graph({0, 1}, {(1, 'next'): 0}, {'sl.list.null': 0, 'x': 1}), Graph({0}, {}, {'sl.list.null': 0, 'x': 0}), Graph({0, 1, 2}, {(1, 'next'): 2, (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1})))
True
>>> is_in(eval_(sl.list.seg(x, y)), [Graph({0, 1}, {}, {'sl.list.null': 0, 'x': 1, 'y': 1}), Graph({0, 1, 2}, {(1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2})])
True
>>> eval_(z3.And(sl.list.seg(x, y), sl.list.eq(x, sl.list.null)))
Graph({0}, {}, {'sl.list.null': 0, 'x': 0, 'y': 0})
>>> is_in(eval_(z3.And(sl.list.seg(x, y), z3.Not(sl.list.eq(x, sl.list.null)), z3.Not(sl.list.eq(x, y)))), (Graph({0, 1, 2}, {(1, 'next'): 2}, {'sl.list.null': 0, 'x': 1, 'y': 2}), Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 0, 'x': 1, 'y': 3})))
True
>>> is_in(eval_(sl.list.seg(x, sl.list.null)), [Graph({0}, {}, {'sl.list.null': 0, 'x': 0}), Graph({0, 1}, {(1, 'next'): 0}, {'sl.list.null': 0, 'x': 1})])
True
>>> eval_(sl.sepcon(sl.list.seg(x, sl.list.null), sl.list.neq(x, sl.list.null)))
Graph({0, 1}, {(1, 'next'): 0}, {'sl.list.null': 0, 'x': 1})
>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d)), sl.list(x))); g
Graph({0, 1}, {(1, 'data'): ..., (1, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 0}, {'d': ...})
>>> g.are_equal('x', 'data', 'd')
True

When using the ordinary list predicate, longer lists end in null as well:

>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,z), sl.list.data(y,e)), sl.list(x))); g
Graph({0, 1, 2}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 0}, {'d': ..., 'e': ...})
>>> g.are_equal('x', 'data', 'd')
True
>>> g.are_equal('y', 'data', 'e')
True

With the segment predicate, the stop node is deterministically interpreted as distinct from null (which is fine but not required by our semantics)...

>>> eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,z), sl.list.data(y,e)), sl.list.seg(x, z)))
Graph({0, 1, 2, 3}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 3}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3}, {'d': ..., 'e': ...})

...so we can force it to be null:

>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,z), sl.list.data(y,e), sl.list.eq(z, sl.list.null)), sl.list.seg(x, z))); g
Graph({0, 1, 2}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 0}, {'d': ..., 'e': ...})
>>> g.are_equal('x', 'data', 'd') and g.are_equal('y', 'data', 'e')
True

>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,z), sl.list.data(y,e), sl.list.eq(sl.list.null,z)), sl.list.seg(x, z))); g
Graph({0, 1, 2}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 0}, {'d': ..., 'e': ...})
>>> g.are_equal('x', 'data', 'd') and g.are_equal('y', 'data', 'e')
True

>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,sl.list.null), sl.list.data(y,e)), sl.list(x))); g
Graph({0, 1, 2}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': ..., 'e': ...})
>>> g.are_equal('x', 'data', 'd') and g.are_equal('y', 'data', 'e')
True

Multiple list calls
-------------------

Using the same head twice implies the list is empty:

>>> is_in(eval_(sl.sepcon(sl.list(x), sl.list(x))), [Graph({0}, {}, {'sl.list.null': 0, 'x': 0}), Graph({0, 1}, {}, {'sl.list.null': 0, 'x': 1})])
True
>>> eval_(sl.sepcon(sl.list.seg(x,y), sl.list.seg(x,y)))
Graph({0, 1}, {}, {'sl.list.null': 0, 'x': 1, 'y': 1})
>>> is_sat(sl.sepcon(sl.list.seg(x,y), sl.list.seg(x,y), sl.list.neq(x,y)))
False

Using different heads leads to separate structures:

>>> g = eval_(sl.sepcon(list_ptr_seq(x, sl.list.null, 2), list_ptr_seq(y, sl.list.null, 2, loc_prefix='b', data_prefix='e'))); print_all_named_ptrs(g)
a1 -[next]-> sl.list.null, b1 -[next]-> sl.list.null, x -[next]-> a1, y -[next]-> b1
>>> g = eval_(sl.sepcon(list_ptr_seq(x, sl.list.null, 2), list_ptr_seq(y, sl.list.null, 2, loc_prefix='b', data_prefix='e'), list_ptr_seq(z, sl.list.null, 2, loc_prefix='c', data_prefix='f'))); print_all_named_ptrs(g)
a1 -[next]-> sl.list.null, b1 -[next]-> sl.list.null, c1 -[next]-> sl.list.null, x -[next]-> a1, y -[next]-> b1, z -[next]-> c1

With negation:

>>> is_sat(z3.And(sl.list(x), z3.Not(sl.sepcon(sl.list.seg(x,y), sl.list(y)))))
True

List calls with data
--------------------

Unary:

>>> eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,sl.list.null), sl.list.data(y,e)), sl.list.dpred.unary(sl.alpha == 123, x)))
Graph({0, 1, 2}, {(1, 'data'): 123, (1, 'next'): 2, (2, 'data'): 123, (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': 123, 'e': 123})

Binary (but allocation of only one list node is permissible, so the binary predicate need not hold for the pair (d,e))

>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,sl.list.null), sl.list.data(y,e)), sl.list.dpred.next(sl.alpha > 10*sl.beta, x)), override_bound = 4); g
Graph({0, 1, 2}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2}, {'d': ..., 'e': ...})
>>> g.are_equal('x', 'data', 'd') and g.are_equal('y', 'data', 'e')
True

Binary (both x and y are allocated within the list, so the binary predicate must hold for the pair (d,e))

>>> g = eval_(z3.And(sl.sepcon(sl.list.pointsto(x,y), sl.list.data(x,d), sl.list.pointsto(y,z), sl.list.data(y,e), sl.list.pointsto(z,sl.list.null), sl.list.data(z,f)), sl.list.dpred.next(sl.alpha > 10*sl.beta, x)), override_bound = 4); g
Graph({0, 1, 2, 3}, {(1, 'data'): ..., (1, 'next'): 2, (2, 'data'): ..., (2, 'next'): 3, (3, 'data'): ..., (3, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3}, {'d': ..., 'e': ..., 'f': ...})
>>> all([g.are_equal('x', 'data', 'd'), g.are_equal('y', 'data', 'e'), g.are_equal('z', 'data', 'f')])
True
>>> g.data['d'] > 10 * g.data['e']
True

Tree calls
----------

>>> is_in(eval_(sl.tree(t)), (Graph({0}, {}, {'sl.tree.null': 0, 't': 0}), Graph({0, 1}, {(1, 'left'): 0, (1, 'right'): 0}, {'sl.tree.null': 0, 't': 1})))
True
>>> is_in(eval_(sl.tree.seg2(t, u, v), override_bound = 4), [Graph({0, 1, 2, 3}, {(1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3}), Graph({0, 1, 2, 3, 4, 5}, {(1, 'left'): 0, (1, 'right'): 2, (2, 'left'): 3, (2, 'right'): 5, (3, 'left'): 0, (3, 'right'): 4}, {'sl.tree.null': 0, 't': 1, 'u': 4, 'v': 5}), Graph({0, 1, 2, 3, 4}, {(1, 'left'): 0, (1, 'right'): 2, (2, 'left'): 3, (2, 'right'): 0, (3, 'left'): 0, (3, 'right'): 4}, {'sl.tree.null': 0, 't': 1, 'u': 0, 'v': 4}), Graph({0, 1, 2, 3, 4, 5}, {(1, 'left'): 2, (1, 'right'): 0, (2, 'left'): 0, (2, 'right'): 3, (3, 'left'): 4, (3, 'right'): 5}, {'sl.tree.null': 0, 't': 1, 'u': 4, 'v': 5})])
True
>>> eval_(sl.sepcon(sl.tree.seg2(t, u, v), sl.tree.neq(u, sl.tree.null), sl.tree.neq(v, sl.tree.null)), override_bound = 1)
Graph({0, 1, 2, 3}, {(1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3})
>>> is_in(eval_(sl.tree.dpred.unary2(sl.alpha == 99, t, u, v)), [Graph({0, 1, 2, 3}, {(1, 'data'): 99, (1, 'left'): 2, (1, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 2, 'v': 3}), Graph({0, 1, 2, 3, 4}, {(0, 'data'): 99, (0, 'left'): 1, (0, 'right'): 1, (2, 'data'): 99, (2, 'left'): 3, (2, 'right'): 1, (4, 'data'): 99, (4, 'left'): 0, (4, 'right'): 2}, {'a1': 0, 'a2': 2, 'sl.tree.null': 1, 't': 4, 'u': 3, 'v': 1}, {'d0': 99, 'd1': 99, 'd2': 99}), Graph({0, 1, 2, 3}, {(1, 'data'): 99, (1, 'left'): 2, (1, 'right'): 0, (2, 'data'): 99, (2, 'left'): 0, (2, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 3, 'v': 0}), Graph({0, 1, 2, 3}, {(1, 'data'): 99, (1, 'left'): 2, (1, 'right'): 0, (2, 'data'): 99, (2, 'left'): 0, (2, 'right'): 3}, {'sl.tree.null': 0, 't': 1, 'u': 0, 'v': 3})])
True
>>> is_in(eval_(sl.sepcon(sl.tree(t), sl.tree(t))), [Graph({0}, {}, {'sl.tree.null': 0, 't': 0}), Graph({0, 1}, {}, {'sl.tree.null': 0, 't': 1})])
True
>>> is_sat(sl.sepcon(sl.tree(t), sl.tree.pointsto(t,u,v)))
False
>>> is_sat(sl.sepcon(sl.tree(t), sl.tree.left(t,u)))
False

Further tress tests with fixed (small) size bound enforced by
classically conjoining allocation of three pointers:

(Multiple results are possible depending on whether null is different
from u and v, is the same as u or is the same as v.)

>>> alloc3 = full_tree_fragment(t, [u, v], 3)
>>> g = eval_(z3.And(alloc3, sl.tree.dpred.unary2(sl.alpha == 99, t, u, v))); is_in(g, [Graph({0, 1, 2, 3, 4}, {(0, 'data'): 99, (0, 'left'): 1, (0, 'right'): 1, (2, 'data'): 99, (2, 'left'): 1, (2, 'right'): 3, (4, 'data'): 99, (4, 'left'): 0, (4, 'right'): 2}, {'a1': 0, 'a2': 2, 'sl.tree.null': 1, 't': 4, 'u': 1, 'v': 3}, {'d0': 99, 'd1': 99, 'd2': 99}), Graph({0, 1, 2, 3, 4, 5}, {(0, 'data'): 99, (0, 'left'): 1, (0, 'right'): 1, (2, 'data'): 99, (2, 'left'): 3, (2, 'right'): 4, (5, 'data'): 99, (5, 'left'): 0, (5, 'right'): 2}, {'a1': 0, 'a2': 2, 'sl.tree.null': 1, 't': 5, 'u': 3, 'v': 4}, {'d0': 99, 'd1': 99, 'd2': 99})])
True
>>> g = eval_(z3.And(alloc3, sl.tree.dpred.left2(sl.alpha < sl.beta, t, u, v))); is_in(set(g.all_named_ptrs()), [{('t', 'left', 'a1'), ('t', 'right', 'a2'), ('a1', 'right', 'u'), ('a2', 'right', 'v'), ('a1', 'right', 'sl.tree.null'), ('a1', 'left', 'u'), ('a1', 'left', 'sl.tree.null'), ('a2', 'left', 'u'), ('a2', 'left', 'sl.tree.null')}, {('a2', 'right', 'v'), ('a2', 'left', 'u'), ('t', 'left', 'a1'), ('a1', 'left', 'sl.tree.null'), ('a1', 'right', 'sl.tree.null'), ('t', 'right', 'a2')}])
True
>>> g.data['d0'] < g.data['d1']
True
>>> g = eval_(z3.And(alloc3, sl.tree.dpred.left2(sl.alpha < sl.beta, t, u, v), sl.tree.dpred.right2(sl.alpha > sl.beta + 3, t, u, v))); is_in(set(g.all_named_ptrs()), [{('t', 'right', 'a2'), ('a2', 'left', 'u'), ('a1', 'left', 'sl.tree.null'), ('t', 'left', 'a1'), ('a1', 'right', 'sl.tree.null'), ('a2', 'right', 'v')}, {('a1', 'left', 'u'), ('a2', 'right', 'v'), ('a2', 'left', 'u'), ('t', 'left', 'a1'), ('a1', 'left', 'sl.tree.null'), ('a1', 'right', 'sl.tree.null'), ('t', 'right', 'a2'), ('a2', 'left', 'sl.tree.null'), ('a1', 'right', 'u')}, {('a1', 'left', 'sl.tree.null'), ('a1', 'left', 'v'), ('a1', 'right', 'sl.tree.null'), ('a1', 'right', 'v'), ('a2', 'left', 'u'), ('a2', 'right', 'sl.tree.null'), ('a2', 'right', 'v'), ('t', 'left', 'a1'), ('t', 'right', 'a2')}])
True
>>> g.data['d0'] < g.data['d1'] and g.data['d0'] > g.data['d2'] + 3
True

Unsat calls
-----------

>>> is_sat(z3.And(sl.list(x), z3.Not(sl.list(x))))
False

Equal stop nodes:

>>> is_sat(sl.sepcon(sl.tree.seg2(t, u, v), sl.tree.neq(u, sl.tree.null), sl.tree.neq(v, sl.tree.null), sl.tree.eq(u, v)))
False

Stop nodes in wrong order:

>>> is_sat(z3.And(sl.tree.pointsto(t,v,u), sl.tree.seg2(t, u, v)))
False

Mixed structures
----------------

>>> g = eval_(sl.sepcon(sl.tree.seg(t,u), sl.list.seg(x,y), sl.list.neq(x,y), sl.tree.neq(t,u)))

Many different models are possible. But in all these models, the
source nodes are allocated...

>>> [g.is_alloced('x','next'), g.is_alloced('t','left'), g.is_alloced('t','right')]
[True, True, True]

...and all nodes are different. (In particular, this implies that tree
and list nodes don't coincide.)

>>> len({g.s[v] for v in 'xytu'})
4

A mixed assertion where the allocation is fully determined through a
classical conjunction:

>>> g = eval_(z3.And(sl.sepcon(full_tree_fragment(t, [], 1, loc_prefix = 't', data_prefix = 'td'), list_ptr_seq(x, sl.list.null, 2)), sl.sepcon(sl.tree(t), sl.list(x)))); print_all_named_ptrs(g)
a1 -[next]-> sl.list.null, t -[left]-> sl.tree.null, t -[right]-> sl.tree.null, x -[next]-> a1

"""

import functools, itertools

from z3 import And, Not, Or
from .. import serialization
from ..utils import utils, logger
from ..z3api import z3utils
from . import astutils
from . import constraints as c
from . import shared
from . import slast

def as_split_constraints(A, B, ast, fresh = None):
    assert isinstance(A, c.SmtConstraint)
    assert isinstance(B, c.SmtConstraint)
    expr = ast.to_sl_expr()
    A.sl_expr = expr
    A.description = 'Structural part (A)'
    B.sl_expr = expr
    B.description = 'Definitional part (B)'
    if fresh is None:
        fresh = set()
    return shared.SplitEnc(A, B, fresh)

def encode_ast(config, ast):
    config.next_fp_ix = 0 # Reset the next free FP id to 0 for consistent naming
    X = config.global_symbols.X_vec()
    A, B, Z = encode_boolean(config, X, ast)
    A = c.And(A, description = '***** A (bound: {}) *****'.format(config.n))
    B = c.And(B, description = '***** B (bound: {}) *****'.format(config.n))
    cs = [A,B]
    cs.append(config.global_constraint())
    consts = astutils.consts_by_struct(ast)
    dconsts = astutils.data_consts(ast)
    heap_funs = itertools.chain(*(s.heap_fns() for s in config.structs))
    nulls = [struct.null for struct in config.structs]
    decls = set(itertools.chain(Z,
                                X.all_fps(), # X_f for all fields f
                                [config.global_symbols.X()] if config.structs else [], # Union of X_f (if there's any structure)
                                *consts.values(),
                                dconsts,
                                nulls,
                                heap_funs))
    return c.Z3Input(constraint = c.And(*cs),
                     decls = decls,
                     encoded_ast = ast)

def encode_boolean(config, X, ast):
    type_ = type(ast)
    if type_ is slast.SlAnd:
        return encode_and(config, X, ast)
    elif type_ is slast.SlOr:
        return encode_or(config, X, ast)
    elif type_ is slast.SlNot:
        return encode_not(config, X, ast)
    else:
        Y = config.get_fresh_fpvector()
        A, B, Z1 = encode_spatial(config, ast, Y)
        connection = c.And(*all_equal(Y, X),
                           description = 'Connecting spatial formula to global constraint')
        A = c.And(A, connection,
                  description = 'Placing {} in the global context'.format(serialization.expr_to_smt2_string(ast.to_sl_expr(), multi_line = False)))
        # B = c.And(B, connection,
        #           description = 'Placing {} in the global context'.format(serialization.expr_to_smt2_string(ast.to_sl_expr(), multi_line = False)))
        Z = Z1.union(Y.all_fps())
        return shared.SplitEnc(A, B, Z)

def encode_spatial(config, ast, Y):
    type_ = type(ast)
    if type_ == slast.SepCon:
        return encode_sepcon(config, ast, Y)
    elif type_ == slast.PredCall:
        return config.encode_call(ast, Y)
    elif type_ == slast.DataAtom:
        return encode_data_atom(ast, Y)
    elif type_ == slast.PointsTo:
        return encode_pto(ast, Y)
    elif type_ == slast.DPointsTo:
        return encode_dpto(ast, Y)
    elif type_ == slast.PointsToSingleField:
        return encode_pto_fld(ast, Y)
    elif type_ == slast.SpatialEq:
        return encode_eq(ast, Y)
    else:
        msg = 'No encoder defined for {}'
        raise utils.SlothException(msg.format(type_))

def encode_eq(eq, Y):
    expr = eq.left == eq.right
    if eq.negated:
        expr = Not(expr)
    A = c.as_constraint(expr)
    B = c.And(*(fp.is_empty() for fp in Y.all_fps()))
    return as_split_constraints(A, B, eq)

def encode_data_atom(da, Y):
    A = c.as_constraint(da.atom)
    B = c.And(*(fp.is_empty() for fp in Y.all_fps()))
    return as_split_constraints(A, B, da)

def encode_pto_fld(pto, Y):
    return _encode_field_alloc([pto.fld], pto, Y)

def encode_pto(pto, Y):
    return _encode_field_alloc(pto.struct.points_to_fields, pto, Y)

def encode_dpto(pto, Y):
    return _encode_field_alloc(pto.struct.ordered_fields, pto, Y)

def _encode_field_alloc(flds, pto, Y):
    struct, src, trgs = pto.struct, pto.src, pto.trgs
    alloced, empty = Y.group_by_flds(flds)
    assert len(alloced) == len(flds)
    assert len(flds) == len(trgs)
    A = c.And(Not(src == struct.null),
              *(trg == struct.heap_fn(fld)(src) for fld, trg in zip(flds, trgs)))
    B = c.And(*(fp.is_singleton(src) for fp in alloced),
              *(fp.is_empty() for fp in empty))
    return as_split_constraints(A, B, pto)

def all_disjoint(Y1, Y2):
    assert len(Y1) == len(Y2)
    for fld in Y1:
        yield Y1[fld].disjoint_from(Y2[fld])

def all_equal(Y1, Y2):
    assert len(Y1) == len(Y2)
    for fld in Y1:
        yield Y1[fld].is_identical(Y2[fld])

def all_union(Y, Y1, Y2):
    assert len(Y1) == len(Y2) and len(Y) == len(Y1)
    for fld in Y:
        yield Y[fld].union_of(Y1[fld], Y2[fld])

def encode_sepcon(config, sc, Y):
    Y1 = config.get_fresh_fpvector()
    A1, B1, Z1 = encode_spatial(config, sc.left, Y1)
    Y2 = config.get_fresh_fpvector()
    A2, B2, Z2 = encode_spatial(config, sc.right, Y2)

    disjointness = c.And(*all_disjoint(Y1, Y2),
                         description = 'Sepcon operands have disjoint footprints')
    A = c.And(A1, A2, disjointness)

    union = c.And(*all_union(Y, Y1, Y2),
                  description = 'Sepcon operand footprints combine into global footprint')
    B = c.And(B1, B2, union)
    return as_split_constraints(A, B, sc, fresh = Z1.union(Z2).union(Y1.all_fps()).union(Y2.all_fps()))

def encode_binop(op, config, X, ast):
    A1, B1, Z1 = encode_boolean(config, X, ast.left)
    A2, B2, Z2 = encode_boolean(config, X, ast.right)
    A = op(A1, A2)
    B = c.And(B1, B2)
    return as_split_constraints(A, B, ast, fresh = Z1.union(Z2))

encode_and = functools.partial(encode_binop, c.And)
encode_or = functools.partial(encode_binop, c.Or)

def encode_not(config, X, ast):
    A1, B, Z = encode_boolean(config, X, ast.arg)
    A = c.Not(A1)
    return as_split_constraints(A, B, ast, fresh = Z)
