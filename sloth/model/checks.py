"""

.. testsetup::

   from sloth import *
   from sloth.model.checks import *

"""

import itertools

from .. import z3api
from ..encoder import encoder
from ..utils import utils
from . import model as model_mod
from .graph import Graph, canonicalize, DATA_FLD

def _as_graph(m):
    if isinstance(m, Graph):
        return m
    elif isinstance(m, model_mod.SmtModel):
        return graph_from_smt_model(m)
    else:
        msg = "Can't construct graph from {}"
        raise utils.SlothException(msg.format(type(m).__name__))

def isomorphic(m1, m2):
    """
    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null))
    >>> m = model(sl_expr)
    >>> isomorphic(m, Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 0}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3}))
    True
    >>> isomorphic(m, Graph({0, 1, 2, 3}, {(1, 'next'): 2, (2, 'next'): 3, (3, 'next'): 1}, {'sl.list.null': 0, 'x': 1, 'y': 2, 'z': 3}))
    False

    """
    g1 = _as_graph(m1)
    g2 = _as_graph(m2)
    return canonicalize(g1) == canonicalize(g2)

def canonical_graph(m, ignore_null = False):
    g = graph_from_smt_model(m, ignore_null)
    #print('Non-canonical graph:\n{}'.format(g))
    return canonicalize(g)

def is_aux_var(x):
    # TODO: This naming scheme should not be hardcoded here!
    s = str(x)
    try:
        return s[0] == 'x' and int(s[1:]) >= 0
    except:
        return False

def graph_from_smt_model(m, ignore_null = False, skip_fn = is_aux_var):
    """Construct a graph model from an SMT model.

    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null))
    >>> m = model(sl_expr)
    >>> print(graph_from_smt_model(m))
    Graph[
      0: [x] -[next]> 1
      1: [y] -[next]> 2
      2: [z] -[next]> 3
      3: [sl.list.null] ->
    ]

    """
    # TODO: Split into smaller parts

    vals = set()
    ptrs = {}
    stack = {}
    for s, sm in m.struct_models.items():
        vals.update(map(lambda l: l.as_long(), sm.locs))
        if not ignore_null:
            null = sm.null()
            try:
                null_val = null.as_long()
            except AttributeError:
                # Sometimes z3 may not interpret null (if it's not relevant for the query)
                # That's fine, we'll not add null to the graph then.
                pass
            else:
                # Null is in the model => Add to graph
                vals.add(null_val)
                stack[str(s.null)] = null_val

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
        if not skip_fn(c):
            try:
                int_val = v_ref.as_long()
            except:
                # FP var or reachability func interpretation => Skip
                pass
            else:
                data[str(c)] = int_val

    # Filter out isolated nodes
    non_isolated = set(itertools.chain(stack.values(),
                               (src for src,_ in ptrs),
                               (trg for (_,lbl), trg in ptrs.items() if lbl != DATA_FLD)
                               ))
    assert non_isolated.issubset(vals), \
        'Trying to restrict {} to {}, which is not a subset'.format(Graph(vals, ptrs, stack, data), non_isolated)
    return Graph(non_isolated, ptrs, stack, data)
