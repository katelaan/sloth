"""

.. testsetup::

   from sloth import *
   from sloth.model.checks import *

"""

import itertools

from .. import consts
from ..utils import utils
from . import model as model_mod
from .graph import Graph, canonicalize

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
    return str(x).startswith(consts.AUX_VAR_PREFIX)

def graph_from_smt_model(m, ignore_null = False, skip_fn = is_aux_var, with_tree_edges_to_null = False):
    """Construct a graph model from an SMT model.

    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null)); m = model(sl_expr)
    >>> graph_from_smt_model(m) in (Graph({0, 1, 2, 3}, {(0, 'next'): 1, (1, 'next'): 2, (3, 'next'): 0}, {'sl.list.null': 2, 'x': 3, 'y': 0, 'z': 1}),Graph({0, 1, 2, 3}, {(0, 'next'): 1, (1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 3, 'x': 0, 'y': 1, 'z': 2}))
    True

    """
    # TODO: Split this monster of a method into smaller parts

    vals = set()
    ptrs = {}
    stack = {}
    for s, sm in m.struct_models.items():
        skip_null_edges = (s.unqualified_name == consts.TREE_PRED
                           and not with_tree_edges_to_null)

        vals.update(map(lambda l: l.as_long(), sm.locs))

        null = sm.null()
        try:
            null_val = null.as_long()
        except AttributeError:
            # Sometimes z3 may not interpret null (if it isn't relevant for the query)
            # That's fine, we'll not add null to the graph then.
            null_val = None
        else:
            if not ignore_null and not skip_null_edges:
                # Null is in the model => Add to graph
                vals.add(null_val)
                stack[str(s.null)] = null_val
            else:
                vals.discard(null_val)

        # Add every (non-null) constant to the stack
        # Null was already dealt with above
        for c in sm.loc_consts():
            if str(c) == str(s.null):
                continue
            v = m.val_of(c).as_long()
            #print('{} : {}'.format(c, v))
            stack[str(c)] = v
            # Add all pointers for all fields of the structure

        #null_reachable = False

        # Add all pointers by looping over all fields and all locations
        for fld in s.fields:
            fn = sm.heap_fn(fld)
            if fn.is_defined():
                for loc in sm.locs:
                    if sm.is_alloced(loc, fld):
                        #print('{} : {} -[{}]> {}'.format(loc, type(loc).__name__, fld, fn(loc)))
                        src = loc.as_long()
                        #print('{} {}'.format(loc, fn(loc)))
                        try:
                            trg = fn(loc).as_long()
                        except AttributeError:
                            raise Exception("During lookup of {} : {} in {}: Can't convert {} : {} to long".format(loc, type(loc).__name__, fn, fn(loc), type(fn(loc)).__name__)) from None
                        else:
                            if (not skip_null_edges) or trg != null_val:
                               ptrs[(src, fld)] = trg
                    else:
                        pass

        # (Very inefficiently) delete all vars that don't occur in the graph
        to_delete = []
        for c, v in stack.items():
            match = False
            for (src, _), trg in ptrs.items():
                if src == v or trg == v:
                    match = True
                    break
            if not match:
                to_delete.append(c)
        for c in to_delete:
            del stack[c]

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
                               (trg for (_,lbl), trg in ptrs.items() if lbl != consts.FLD_DATA)
                               ))
    assert non_isolated.issubset(vals), \
        'Trying to restrict {} to {}, which is not a subset'.format(Graph(vals, ptrs, stack, data), non_isolated)
    return Graph(non_isolated, ptrs, stack, data)
