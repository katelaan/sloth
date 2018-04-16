"""

.. testsetup::

   from sloth.model.graph import *

"""

import functools, itertools

from ..utils import utils

DATA_FLD = 'data'

@functools.total_ordering
class Graph:
    """Represents a model from our model algebra.

    >>> m1 = graph_from_edge('x', 'n', 'y')
    >>> m2 = graph_from_edge('y', 'n', 'x2')
    >>> print(m1 * m2)
    Graph[
      0: [x] -[n]> 1
      1: [y] -[n]> 2
      2: [x2] ->
    ]

    >>> m1 = Graph({0,1}, {(0,'n'):1}, {'x1':0,'y1':1})
    >>> m2 = Graph({0,1,2}, {(0,'n'):1,(1,'n'):2}, {'y1':0,'x2':2})
    >>> print(m1 * m2)
    Graph[
      0: [x1] -[n]> 1
      1: [y1] -[n]> 2
      2: -[n]> 3
      3: [x2] ->
    ]

    >>> m1 = Graph({0,1,2}, {(0,'n'):1,(1,'n'):2}, {'x1':0,'y1':1,'y2':2})
    >>> m2 = Graph({0,1,2,3}, {(0,'n'):1,(1,'n'):2,(2,'n'):3}, {'y2':0,'x2':3})
    >>> print(m1 * m2)
    Graph[
      0: [x1] -[n]> 1
      1: [y1] -[n]> 2
      2: [y2] -[n]> 3
      3: -[n]> 4
      4: -[n]> 5
      5: [x2] ->
    ]

    """

    def __init__(self, val, ptr, s, data = {}):
        self.val = set(val)
        # TODO: It's worth thinking about a smarter ptr representation, because finding all pointers originating in v is in Theta(len(ptr)) in the current implementation
        self.ptr = dict(ptr)
        self.s = dict(s)
        self.data = dict(data)
        assert self.val.issuperset(k[0] for k in self.ptr), \
            'There is a pointer among {} whose source is not in {}.'.foramt(self.ptr, self.val)
        # TODO: Do we want any special treatment of data pointers? If so, we could reactivate the following assertions.
        #assert self.val.issuperset(self.ptr.values())
        #assert self.val.issuperset(self.s.values())

    def __hash__(self):
        return hash((tuple(sorted(self.val)),
                     tuple(sorted(self.ptr.items())),
                     tuple(sorted(self.s.items())),
                     tuple(sorted(self.data.items()))))

    def __eq__(self, other):
        return all([isinstance(other, Graph),
                    self.val == other.val,
                    self.ptr == other.ptr,
                    self.s == other.s,
                    self.data == other.data])

    def __len__(self):
        return len(self.ptr)

    def __iter__(self):
        return iter(self.ptr)

    def __lt__(self, other):
        # Note the ordering defined by this + eq doesn't make a lot of
        # sense. I defined it like this because that's currently
        # sufficient to guarantee a stable ordering of the output of
        # the test cases, see e.g. print_joined
        return any(
            len(self.ptr) < len(other.ptr),
            len(self.val) < len(other.val),
            len(self.s) < len(other.s),
            len(self.data) < len(other.data))

    def __mul__(self, other):
        """Separating conjunction.

        """
        blocked = set(self.val)
        def free_gen():
            i = 0
            while True:
                if i not in blocked:
                    yield i
                i += 1

        #print('Blocked: {}'.format(blocked))

        # Rename everything that is not shared
        shared_vars = set(x for x in self.s if x in other.s)
        #print('Shared: {}'.format(shared_vars))
        vals_for_sharing = set(other.s[x] for x in other.s if x in shared_vars)
        #print('Shared vals: {}'.format(vals_for_sharing))

        renaming = dict()
        free_vals = free_gen()
        for otherv in other.val - vals_for_sharing:
            if otherv in blocked:
                new_val = next(free_vals)
                blocked.add(new_val)
                #print('Renaming {} to {}'.format(otherv, new_val))
                renaming[otherv] = new_val
        for x in shared_vars:
            renaming[other.s[x]] = self.s[x]
        #print('Full renaming: {}'.format(renaming))
        disjoint = other.rename_vals(renaming)
        #print('Graph after renaming: {}'.format(disjoint))
        return self.merge(disjoint)

    def rename_vals(self, renaming):
        def renamed(v):
            return renaming.get(v,v)
        new_val = {renamed(v) for v in self.val}
        new_ptr = {(renamed(src),lbl) : renamed(trg)
                   for (src,lbl),trg in self.ptr.items()}
        new_s = {k : renamed(v) for k,v, in self.s.items()}
        new_d = dict(self.data)
        return Graph(new_val, new_ptr, new_s, new_d)

    def merge(self, other):
        merged_val = self.val.union(other.val)
        merged_ptr = dict(self.ptr)
        merged_ptr.update(other.ptr)
        merged_s = dict(self.s)
        merged_s.update(other.s)
        merged_data = dict(self.data)
        merged_data.update(other.data)
        return Graph(merged_val, merged_ptr, merged_s, merged_data)

    def ptr_flds(self):
        """
        >>> m = Graph({0, 1, 2, 3, 5, 6, 7}, {(0, 'm'): 1, (0, 's'): 2, (1, 'm'): 3, (7, 'l'): 6, (7, 'r'): 5}, {'x1': 7, 'x2': 5, 'x3': 0})
        >>> m.ptr_flds() == {'l','m','r','s'}
        True

        """
        return {lbl for (_,lbl) in self.ptr}

    def ptrs_by_fld(self):
        """
        >>> m = Graph({0, 1, 2, 3, 5, 6, 7}, {(0, 'm'): 1, (0, 's'): 2, (1, 'm'): 3, (7, 'l'): 6, (7, 'r'): 5}, {'x1': 7, 'x2': 5, 'x3': 0})
        >>> utils.print_unique_repr(m.ptrs_by_fld()) # doctest: +ELLIPSIS
        {'l': [((7, 'l'), 6)],..., 's': [((0, 's'), 2)]}
        """
        lbl_key = lambda i:i[0][1]
        ptr_sorted = [i for i in sorted(self.ptr.items(), key = lbl_key)]
        return {key : list(grp)
                for key,grp in itertools.groupby(ptr_sorted, lbl_key)}

    def alloced_flds(self, v):
        """
        >>> m = Graph({0, 1, 2, 3, 5, 6, 7}, {(0, 'm'): 1, (0, 's'): 2, (1, 'm'): 3, (7, 'l'): 6, (7, 'r'): 5}, {'x1': 7, 'x2': 5, 'x3': 0})
        >>> m.alloced_flds(0) == {'m','s'}
        True
        """
        return {lbl for (w, lbl) in self.ptr if w == v}

    def add_var(self, x, v):
        """
        >>> Graph({0, 1, 2}, {(0, 'n'): 1, (1, 'n'): 2}, {'x1': 0}).add_var('x2', 2)
        Graph({0, 1, 2}, {(0, 'n'): 1, (1, 'n'): 2}, {'x1': 0, 'x2': 2})
        >>> Graph({0, 1, 2}, {(0, 'n'): 1, (1, 'n'): 2}, {'x1': 0}).add_var('x1', 2)
        Graph({0, 1, 2}, {(0, 'n'): 1, (1, 'n'): 2}, {'x1': 2})
        """
        s = dict(self.s)
        s[x] = v
        return Graph(self.val, self.ptr, s)

    def are_equal(self, src_var, fld, data_var):
        return self.ptr[(self.s[src_var], fld)] == self.data[data_var]


    def is_garbagefree(self):
        """Returns true iff all members of `val` are reachable from a
variable.

        >>> m1 = Graph({0, 1}, {(0, 'n'): 1}, {'x1': 0, 'x2': 1})
        >>> m2 = Graph({0, 1}, {(1, 'n'): 0}, {'x1': 0})
        >>> m1.is_garbagefree(), m2.is_garbagefree()
        (True, False)

        """
        cache = set(self.s.values())
        visited = set()
        while cache:
            curr = cache.pop()
            visited.add(curr)
            # Only follow non-data pointers
            children = (trg for (src,lbl),trg in self.ptr.items() if src == curr and lbl != DATA_FLD)
            for c in children:
                if c not in visited and c in self.val:
                    cache.add(c)
        return visited == self.val

    def __str__(self):
        def summary(v):
            xs = ', '.join(x for x in self.s if self.s[x] == v)
            if xs:
                xs = '[{}] '.format(xs)
            trgs = ', '.join('-[{}]> {}'.format(lbl,trg)
                             for (src,lbl),trg in sorted(self.ptr.items(),
                                                         key=lambda t:t[0])
                             if src == v)
            if not trgs:
                trgs = '->'
            return '  {}: {}{}'.format(v, xs, trgs)
        ss = (summary(v) for v in sorted(self.val))
        if self.data:
            pairs = ['{} = {}'.format(x,v) for x,v in self.data.items()]
            data = '\n  data: ' + ', '.join(pairs)
        else:
            data = ''

        return 'Graph[\n{}{}\n]'.format('\n'.join(ss), data)

    def __repr__(self):
        fmt = 'Graph({!r}, {}, {}{})'
        ptr_str = utils.unique_repr(self.ptr)
        stack_str = utils.unique_repr(self.s)
        if self.data:
            data_str = ', ' + utils.unique_repr(self.data)
        else:
            data_str = ''
        return fmt.format(self.val, ptr_str, stack_str, data_str)

    def has_ptr(self, src, fld, trg):
        """Return True iff there is a `fld`-pointer between the vars `src` and `trg`.

        >>> m1 = Graph({0, 1}, {(0, 'n'): 1}, {'x1': 0, 'x2': 1}); m1.has_ptr('x1', 'n', 'x2')
        True
        >>> m1.has_ptr('x1', 'p', 'x2') or m1.has_ptr('x2', 'n', 'x1')
        False

        """
        try:
            ptr_trg = self.ptr[(self.s[src], fld)]
        except KeyError:
            return False
        else:
            return ptr_trg == self.s[trg]

    def all_named_ptrs(self, ignore_flds = [DATA_FLD]):
        flds = self.ptr_flds().difference(ignore_flds)
        for src in self.s:
            for trg in self.s:
                for fld in flds:
                    if self.has_ptr(src, fld, trg):
                        yield (src, fld, trg)

def empty_graph(*vs):
    """Return a model without any pointers and with one location per var in `vs`.

    >>> empty_graph()
    Graph(set(), {}, {})
    >>> empty_graph('x1', 'x2', 'x3')
    Graph({0, 1, 2}, {}, {'x1': 0, 'x2': 1, 'x3': 2})
    """
    val = set(range(len(vs)))
    s = dict(zip(vs, range(len(vs))))
    return Graph(val, {}, s)

def graph_from_edge(x, lbl, y):
    """Return a model consisting of a single pointer x -[lbl]> y.

    >>> print(graph_from_edge('x', 'n', 'y'))
    Graph[
      0: [x] -[n]> 1
      1: [y] ->
    ]

    """
    val = {0, 1}
    ptr = {(0,lbl) : 1}
    s = {x : 0, y : 1}
    return Graph(val, ptr, s)

def canonicalize(m):
    """Computes the canonicalization of the graph `m`.

    Assumes that all locations in m are reachable from a variable.

    A canonical model has locations 0,...,N, numbered according
    to their position in a DFS traversal of m starting at the free
    vars (in alphabetic ordering) and always following the pointers in
    alphabetic ordering.

    >>> canonicalize(Graph({3, 5, 0}, {(3, 'n'): 5, (5, 'n'): 0}, {'x1': 3}))
    Graph({0, 1, 2}, {(0, 'n'): 1, (1, 'n'): 2}, {'x1': 0})
    >>> canonicalize(Graph({0, 1, 2, 3, 5, 6, 7}, {(0, 'm'): 1, (0, 's'): 2, (1, 'm'): 3, (7, 'l'): 6, (7, 'r'): 5}, {'x1': 7, 'x2': 5, 'x3': 0}))
    Graph({0, 1, 2, 3, 4, 5, 6}, {(0, 'l'): 1, (0, 'r'): 2, (3, 'm'): 4, (3, 's'): 6, (4, 'm'): 5}, {'x1': 0, 'x2': 2, 'x3': 3})

    """
    assert m.is_garbagefree(), 'The graph {!r} is not garbage free'.format(m)

    renaming = {}
    i = 0
    visited = set()
    cache = [v for _,v in sorted(m.s.items())]

    while cache:
        v, *cache = cache
        if v not in visited:
            renaming[v] = i
            i += 1
            visited.add(v)
            # Add all non-data children to the cache
            children = ((lbl,trg) for (src,lbl),trg in m.ptr.items() if src == v and lbl != DATA_FLD)
            sorted_cs = [trg for (_,trg) in sorted(children)]
            cache = sorted_cs + cache
    return m.rename_vals(renaming)
