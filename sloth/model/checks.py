"""

.. testsetup::

   from sloth import *
   from sloth.encoder import topdown
   from sloth.model.checks import *

"""

from .. import z3api
from ..encoder import topdown
from ..utils import utils
from . import model
from .graph import Graph, canonicalize

def show_evaluation_steps(sl, sl_expr, export_file = None):
    e = topdown.encode_sl_expr(sl, sl_expr)
    print('Constraint:\n-----------')
    print(e.constraint)
    if export_file is not None:
        e.to_file(export_file)
    z3e = e.to_z3_expr()
    print('\n\nAs Z3 expression:\n-----------------')
    print(z3e)
    sat = z3api.is_sat(z3e)
    print('\n\nIs SAT: {}'.format(sat))
    if sat:
        print('\n\nZ3 model:\n---------')
        m = z3api.model()
        print(m)
        print('\n\nAdapted model:\n--------------')
        a = e.label_model(m)
        print(a)
        print('\n\nAs graph:\n---------')
        print(canonical_graph(a))

def _as_graph(m):
    if isinstance(m, Graph):
        return m
    elif isinstance(m, model.SmtModel):
        return graph_from_smt_model(m)
    else:
        msg = "Can't construct graph from {}"
        raise utils.SlothException(msg.format(type(m).__name__))

def isomorphic(m1, m2):
    """
    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null))
    >>> m = topdown.model_of_sl_expr(sl, sl_expr)
    >>> isomorphic(m, Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3}))
    True
    >>> isomorphic(m, Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3}))
    False

    """
    g1 = _as_graph(m1)
    g2 = _as_graph(m2)
    return canonicalize(g1) == canonicalize(g2)

def evaluate_to_graph(sl, sl_expr):
    """
    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null))
    >>> evaluate_to_graph(sl, sl_expr)
    Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3})

    """
    m = topdown.model_of_sl_expr(sl, sl_expr)
    return canonical_graph(m)

def canonical_graph(m):
    return canonicalize(graph_from_smt_model(m))

def graph_from_smt_model(m):
    """Construct a graph model from an SMT model.

    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null))
    >>> m = topdown.model_of_sl_expr(sl, sl_expr)
    >>> print(graph_from_smt_model(m))
    Graph[
      0: [x] -[next]> 1
      1: [y] -[next]> 2
      2: [z] -[next]> 3
      3: [sl.list.null] ->
    ]

    """

    vals = set()
    ptrs = {}
    stack = {}
    for s, sm in m.struct_models.items():
        vals.update(map(lambda l: l.as_long(), sm.locs))
        for c in sm.loc_consts():
            v = m.val_of(c).as_long()
            #print('{} : {}'.format(c, v))
            stack[str(c)] = v
            # Add all pointers for all fields of the structure
            for fld in s.fields:
                fn = sm.heap_fn(fld)
                if fn.is_defined():
                    for loc in sm.locs:
                        if sm.is_alloced(loc, fld):
                            #print('{} : {} -[{}]> {}'.format(loc, type(loc).__name__, fld, fn(loc)))
                            ptrs[(loc.as_long(), fld)] = fn(loc).as_long()
                        else:
                            #print('{}: {} not alloced'.format(loc, fld))
                            pass
    # Add data evaluation to the stack
    data = {}
    for c, v_ref in m.data.items():
        try:
            int_val = v_ref.as_long()
        except:
            # FP var or reachability func interpretation => Skip
            pass
        else:
            data[str(c)] = int_val
    return Graph(vals, ptrs, stack, data)
