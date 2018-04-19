"""Utilities for creating commonly used SL expressions.

.. testsetup::

   from sloth import *
   from sloth.slbuilders import *

"""

import itertools
import z3

from .api import *
from .utils import utils

def list_ptr_seq(src, trg, length, with_data = True, loc_prefix = 'a', data_prefix = 'd'):
    """Return expression for a sequence of `length` pointers from `src` to `trg`.

    Whether or not data allocation is included is controlled by the
    `with_data` flag (True by default).

    >>> x, y = sl.list.locs('x y'); list_ptr_seq(x, y, 2, loc_prefix = 'z_')
    sl.sepcon(sl.sepcon(sl.list.next(x, z_1),
                        sl.list.next(z_1, y)),
              sl.sepcon(sl.list.data(x, d0),
                        sl.list.data(z_1, d1)))
    >>> list_ptr_seq(x, y, 2, loc_prefix = 'z_', with_data = False)
    sl.sepcon(sl.list.next(x, z_1), sl.list.next(z_1, y))

    """
    if length == 0:
        return sl.list.eq(src, trg)

    loc_fmt = loc_prefix + '{}'
    tmp_locs = sl.list.locs(*map(loc_fmt.format, range(1,length)))
    locs = [src] + tmp_locs + [trg]
    ptr_ends = list(utils.consecutive_pairs(locs))
    assert(len(ptr_ends) == length)
    if length > 1:
        expr = sl.sepcon(*(sl.list.next(*pair) for pair in ptr_ends))
    else:
        expr = sl.list.next(*ptr_ends[0])
    if with_data:
        data_fmt = data_prefix + '{}'
        tmp_data = z3.Ints(' '.join(map(data_fmt.format, range(length))))
        assert(len(tmp_data) == len(locs) - 1)
        data_ptrs = zip(locs[:-1], tmp_data)
        if length > 1:
            data_expr = sl.sepcon(*(sl.list.data(*ptr) for ptr in data_ptrs))
        else:
            data_expr = sl.list.data(*next(data_ptrs))
        expr = sl.sepcon(expr, data_expr)
    return expr

def full_tree_fragment(root, stops, size, with_data = True, loc_prefix = 'a', data_prefix = 'd'):
    """Return expression for a tree segment of size `size` rooted in `root`.

    If `stops` is non-empty, the given stop nodes are used as the
    first (but not necessarily left-most) leaves.

    Warning: Stop nodes are in fact reordered if they are spread over
    two levels of the tree.

    Whether or not data allocation is included is controlled by the
    `with_data` flag (True by default).

    >>> t, u, v = sl.tree.locs('t u v'); full_tree_fragment(t, [], 2, with_data = False)
    sl.sepcon(sl.sepcon(sl.tree.left(t, a1),
                        sl.tree.right(t, sl.tree.null)),
              sl.sepcon(sl.tree.left(a1, sl.tree.null),
                        sl.tree.right(a1, sl.tree.null)))
    >>> full_tree_fragment(t, [u, v], 2, with_data = False)
    sl.sepcon(sl.sepcon(sl.tree.left(t, a1),
                        sl.tree.right(t, sl.tree.null)),
              sl.sepcon(sl.tree.left(a1, u),
                        sl.tree.right(a1, v)))
    >>> full_tree_fragment(t, [u, v], 2, with_data = True)
    sl.sepcon(sl.sepcon(sl.tree.left(t, a1),
                        sl.sepcon(sl.tree.right(t, sl.tree.null),
                                  sl.tree.data(t, d0))),
              sl.sepcon(sl.tree.left(a1, u),
                        sl.sepcon(sl.tree.right(a1, v),
                                  sl.tree.data(a1, d1))))

    """
    if size == 0:
        num_stops = len(stops)
        if num_stops == 0:
            return sl.tree.eq(root, sl.tree.null)
        elif num_stops == 1:
            return sl.tree.eq(root, stops[0])
        else:
            return sl.sepcon(*(sl.tree.eq(root, stop) for stop in stops))

    loc_fmt = loc_prefix + '{}'
    tmp_locs = sl.tree.locs(*map(loc_fmt.format, range(1,size)))
    if with_data:
        data_fmt = data_prefix + '{}'
        tmp_data = z3.Ints(' '.join(map(data_fmt.format, range(size))))

    alloced = [root] + tmp_locs
    last_ix = 2*len(alloced)
    reverse_stops = list(reversed(stops))
    LEFT = 1
    RIGHT = 2

    def child(src_ix, direction):
        trg_ix = 2*src_ix + direction
        try:
            return alloced[trg_ix]
        except:
            try:
                return reverse_stops[last_ix-trg_ix]
            except:
                return sl.tree.null

    ptrs = []
    for src_ix, src in enumerate(alloced):
        ptrs.append(sl.tree.left(src, child(src_ix, LEFT)))
        ptrs.append(sl.tree.right(src, child(src_ix, RIGHT)))
        if with_data:
            ptrs.append(sl.tree.data(src, tmp_data[src_ix]))
    return sl.sepcon(*ptrs)
