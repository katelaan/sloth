from igraph import Graph, plot

from .. import consts
from . import model
from ..utils import logger

def plot_model(smt_model, draw_isolated_nodes):
    plotter = Plotter(smt_model, draw_isolated_nodes)
    plotter.run()

class Plotter(object):

    def __init__(self, model, draw_isolated_nodes):
        self.model = model
        self.draw_isolated_nodes = draw_isolated_nodes

    def run(self):
        self.fill_graph()
        logger.debug("Graph representation: {}".format(self.g))
        self.prune_graph()
        logger.debug("Graph representation after pruning: {}".format(self.g))
        self.layout_graph()

    def fill_graph(self):
        self.g = Graph(directed=True)
        self.g.add_vertices(len(self.model))
        self.int_to_node = dict(enumerate(self.model.typed_locs()))
        logger.debug("Mapping from graph vertex ids to model locations:\n{}".format(self.int_to_node))
        self.node_to_int = {v: k for k, v in self.int_to_node.items()}
        logger.debug("Mapping from model locations to vertex ids:\n{}".format(self.node_to_int))

        # Assign variable labels to the vertices
        for key, node in self.int_to_node.items():
            self.g.vs[key]["vars"] = self.model.node_labeling[node]
            self.g.vs[key]["type"] = str(self.int_to_node[key].struct)
        # print(g.vs["vars"])

        for smodel, fld in self.fld_iterator():
            logger.debug("Adding edges for {}".format(smodel.struct.heap_fn(fld)))
            self._add_edges(
                lookup_fn = smodel.heap_fn(fld),
                tagging_fn = model.tag(smodel.struct),
                loc_iter = iter(smodel),
                label = fld)
        #print(g.es["field"])

    def fld_iterator(self):
        for struct in self.model.structs:
            smodel = self.model.struct_model(struct)
            if smodel:
                for fld in struct.points_to_fields:#struct.fields:
                    yield (smodel, fld)

    def null_iterator(self):
        for struct in self.model.structs:
            smodel = self.model.struct_model(struct)
            if smodel.null() is not None:
                yield (smodel, smodel.null())

    def prune_graph(self):
        # For each field, remove the edges from isolated nodes to the default
        # value of the corresponding heap function, because the isolated nodes
        # don't actually play a role in satisfying the formula
        #logger.info(self.g)

        for smodel, fld in self.fld_iterator():
            self._cleanup_edges(
                lookup_fn = smodel.heap_fn(fld),
                tagging_fn = model.tag(smodel.struct),
                field = fld)

        # Remove edges that start in null
        for smodel, null in self.null_iterator():
            self._remove_null_edges(model.tag(smodel.struct), null)

        # Delete isolated node if that option is enabled
        if (not self.draw_isolated_nodes):
            self._delete_isolated_nodes()

    def _remove_null_edges(self, tagging_fn, null_node):
        assert(null_node is not None)
        try:
            edges_from_null = self.g.es.select(_source = self.node_to_int[tagging_fn(null_node)])
        except KeyError:
            msg = "Null node {} not in function interpretation => No null edges to prune"
            logger.debug(msg.format(null_node))
        else:
            self.g.delete_edges(edges_from_null)

    def layout_graph(self):
        # The actual layout
        self.g.vs["label"] = [str(v)[1:-1] for v in self.g.vs["vars"]]
        if self.g.es: self.g.es["label"] = self.g.es["field"]
        self.g.vs["color"] = [self._assign_color(v) for v in self.g.vs]
        self.g.vs["shape"] = [self._assign_shape(v) for v in self.g.vs]
        layout = self.g.layout_auto()
        plot(self.g, layout=layout)

    def _add_edges(self, lookup_fn, tagging_fn, loc_iter, label):
        if lookup_fn.is_defined():
            # Add labeled edges for the heap_left / heap_right functions
            for loc in loc_iter:
                src_vertex = self.node_to_int[tagging_fn(loc)]
                trg = lookup_fn(loc)
                trg_vertex = self.node_to_int[tagging_fn(trg)]
                self.g.add_edge(src_vertex, trg_vertex, field = label)

    def _cleanup_edges(self, lookup_fn, tagging_fn, field):
        if lookup_fn.is_defined():
            # Remove all edges that go from isolated nodes to the default value
            # of the corresponding lookup function
            def_val = self.node_to_int[tagging_fn(lookup_fn.default_val())]
            to_delete = []
            for e in self.g.es.select(field_eq = field, _target = def_val):
                logger.debug("Candidate for removal: {}->{}".format(e.source, e.target))
                if self._remove_edge(e):
                    logger.debug("Will remove edge")
                    to_delete.append(e)
            self.g.delete_edges(to_delete)

    def _remove_edge(self, e):
         return (self.g.vs[e.source]["vars"] == []
                 and len(self.g.es.select(_target = e.source)) == 0)

    def _delete_isolated_nodes(self):
        to_delete = []
        for v in self.g.vs:
            if (len(self.g.es.select(_target = v.index))
                + len(self.g.es.select(_source = v.index)) == 0):
                to_delete.append(v)
        self.g.delete_vertices(to_delete)

    def _assign_color(self, v):
        color_dict = {
            "sl.list": "orange",
            "sl.dlist": "red",
            "sl.tree": "yellow",
            "sl.ptree": "green"
        }
        return color_dict.get(v["type"], "grey")

    def _assign_shape(self, v):
        if consts.NULL_SUFFIX in v["label"]:
            return "rectangle"
        else:
            return "circle"
