from collections import Counter, namedtuple
import functools
import operator

from ..utils import utils

# FIXME: Corner case of singleton self loop component

def component_roots(gm):
    r = var_reachability(gm)
    #print('Var reachability: {}'.format(r))
    srcs = set(r)
    trgls = utils.flatten(r.values())
    trgs = set(trgls)
    trg_mult = Counter(trgls)

    # Everything without incoming edges is a component root
    roots = set(n for n in srcs if n not in trgs)
    # Every source of a cycle is a component root
    roots.update(n for n in srcs if n in r[n])
    # Every shared node is a component root
    roots.update(n for n, mult in trg_mult.items() if mult > 1)
    return roots

def num_incoming(gm, x):
    n = gm.resolve(x)
    return [i[1] for i in gm.ptr.items()].count(n)

def var_reachability(gm, sort = True):
    reach = {}
    visited = set()

    if sort:
        vs = sorted(gm.s, key = functools.partial(num_incoming, gm))
    else:
        vs = sorted(gm.s)

    for x in vs:
        #print('Handling {}'.format(x))
        xv = gm.resolve(x)
        if xv in visited:
            continue
        visited.add(xv)
        cache = gm.successors(xv, FLDS)
        while cache:
            #print('Visited: {}; Cache: {}'.format(visited, cache))
            new_cache = []
            for node in cache:
                labeling_vs = list(gm.vars_at(node))
                for reach_v in labeling_vs:
                    reach.setdefault(x, set()).add(reach_v)

                if node not in visited:
                    new_cache.extend(gm.successors(node, FLDS))

            visited.update(cache)
            cache = new_cache #[n for n in new_cache if n not in visited]

    return reach

def components(gm):
    roots = component_roots(gm)
    #print('Comp roots: {}'.format(roots))
    return rooted_components(gm, roots)

def rooted_components(gm, component_roots):
    comps = {}
    comp_edges = []
    visited_roots = set()

    for x in component_roots:
        v_of_x = gm.resolve(x)
        if v_of_x not in visited_roots:
            is_list = gm.is_alloced(x, 'next')
            comp = Component(root = x, is_list = is_list)
            # Stop adding nodes when we encounter another component root
            vs = add_reachable(comp, gm, x, boundary = component_roots)
            comps[x] = comp
            comp_edges.extend((x, v) for v in vs)
            visited_roots.add(v_of_x)

    return ComponentGraph(comps, comp_edges)

def layout(gm):
    #roots = component_roots(gm)
    #comps = rooted_components(gm, roots)
    comps = components(gm)
    return comps.layout(gm)

FLDS = ['left','right','next']

def add_reachable(comp, gm, root, boundary):
    frontier_vs = set()
    root_val = gm.resolve(root)
    visited = {root_val}
    cache = gm.successors(root_val, FLDS)
    level = 0
    comp.add_node(root_val, 0)
    while cache:
        level += 1
        #print('{}: {}'.format(level, cache))
        visited.update(cache)
        new_cache = []
        for node in cache:
            labeling_vs = set(gm.vars_at(node))
            if not boundary.intersection(labeling_vs):
                # Not yet at the boundary to another component => add to component
                comp.add_node(node, level)

                for succ in gm.successors(node, FLDS):
                    if succ not in visited:
                        new_cache.append(succ)
            else:
                frontier_vs.update(labeling_vs)
        cache = new_cache
    return frontier_vs

Dimensions = namedtuple('Dimensions', 'width height')

def shift(positions, x_shift, y_shift):
    return {
        node : (x + x_shift, y + y_shift) for node, (x, y) in positions.items()
    }

class ComponentGraph:

    def __init__(self, comps, comp_edges):
        self.comps = comps
        self.comp_edges = comp_edges

    def __repr__(self):
        return 'ComponentGraph({!r}, comp_edges = {!r})'.format(self.comps, self.comp_edges)

    def root_comps(self):
        # TODO: Fix this to allow cyclic components
        trgs = set(i[1] for i in self.comp_edges)
        for comp in self.comps.values():
            if comp.root not in trgs:
                yield comp

    def layout(self, gm):
        #print('Laying out {}'.format(self))

        finished = set()
        positions = {}

        top = 0
        top_increment = 0

        num_level = -1
        curr_level = list(self.root_comps())

        while curr_level:
            num_level += 1
            #print('Processing level {}: {}'.format(num_level, curr_level))

            top = top - top_increment
            top_increment = 0
            left = 0

            # Process the current level
            # TODO: This could be further improved by ordering components such that components that share a node in the next level appear next to each other
            for comp in sorted(curr_level, key = operator.attrgetter('root')):
                #print('Level = {}, Top = {}, Left = {}, Laying out {}'.format(num_level, top, left, comp))
                # Layout the next layer of the graph
                zero_based_pos, dimensions = comp.layout(gm)
                #print('Takes up space: {}'.format(dimensions))
                comp_pos = shift(zero_based_pos, left, top)
                positions.update(comp_pos)

                # Compute left border for the next component of the current layer
                left += dimensions.width

                # Compute minimal y value for the next layer
                # TODO: Or min? Which dir do y values increase? Up or down?
                top_increment = max(top_increment, dimensions.height)

            # Compute the next level of components
            finished.update(curr_level)
            srcs = {comp.root for comp in curr_level}
            trgs = {trg for src, trg in self.comp_edges if src in srcs}
            curr_level = [comp for comp in self.comps.values()
                          if (comp.root in trgs) and (not comp in finished)]

        #print(positions)

        assert len(finished) == len(self.comps), \
            "Didn't layout {}".format(set(self.comps.values()).difference(finished))

        return positions


class Component:

    def __init__(self, root, is_list, nodes = None):
        self.root = root
        self.is_list = is_list
        if nodes is None:
            nodes = {}
        self.nodes = nodes

    def __repr__(self):
        name = type(self).__name__
        if self.nodes:
            nodes_str = ', nodes = {}'.format(utils.unique_repr(self.nodes))
        else:
            nodes_str = ''

        return '{}({!r}, is_list={}{})'.format(name, self.root, self.is_list, nodes_str)

    def add_node(self, n, level):
        self.nodes[n] = level

    def layout(self, gm):
        num_lvls = max(self.nodes.values())
        #print('{}-Comp has {} lvls'.format(self.root, num_lvls + 1))

        counts = Counter(i[1] for i in self.nodes.items())
        max_per_level = max(counts.values())
        #print('Max #nodes / lvl: {}'.format(max_per_level))
        # TODO: Better sparseness criterion? Additional difficulty: Ensure that components are always slightly shifted in later levels. Otherwise edges may 'go through' intermediate nodes!
        #is_sparse = max_per_level < max(2, 2 ** (num_lvls - 1))
        #if is_sparse:
        #    print('The component is sparse.')
        #    width = max_per_level
        #else:
        #    width = 2 ** num_lvls
        if self.is_list:
            width = 1
        else:
            width = 2 ** num_lvls
        dim = Dimensions(height = 2*num_lvls + 1, width = width)

        def xpos(lvl, pos_in_lvl):
            if self.is_list:
                multiplier = 1
            else:
                multiplier = width / (lvl+2)
            return multiplier * (1 + pos_in_lvl)

        positions = {}
        level = 0
        # TODO: Keep track of positions even here to make it possible to skip positions!
        nodes = [gm.resolve(self.root)]
        visited = set()
        while nodes:
            visited.update(nodes)
            next_nodes = []
            for pos_in_lvl, node in enumerate(nodes):
                positions[node] = (xpos(level, pos_in_lvl), - 2 * level - 1)
                for fld in FLDS:
                    trg = gm.succ_of(node, fld)
                    if trg is not None and trg in self.nodes and trg not in visited:
                        next_nodes.append(trg)

            nodes = next_nodes
            level += 1

        assert visited == set(self.nodes), 'Visited {} != contained {}'.format(visited, set(self.nodes))

        #print('Unshifted: {}'.format(positions))

        return positions, dim

    def pairs(self):
        return self.pos.items()
