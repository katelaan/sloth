import networkx as nx
import plotly.offline as offline
import plotly.graph_objs as go

from .. import consts
from . import checks
from . import graph

def models_to_html(ms, filename = None):
    title = ''
    body = '\n\n'.join(plot_model(m) for m in ms)
    html = _html_template.format(title=title, body=body)

    if filename is not None:
        with open(filename, 'w') as f:
            f.write(html)
    else:
        return html

_html_template = """<!DOCTYPE html>
<html lang="en-US">
  <head>
    <meta charset="UTF-8">
    <title>{title}</title>
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <script type="text/javascript"
            src="https://cdn.plot.ly/plotly-latest.min.js">
    </script>
  </head>
  <body>
      {body}
  </body>
</html>
"""

def plot_model(m, draw_tree_edges_to_null = False):
    g = model_to_nx_graph(m, draw_tree_edges_to_null = draw_tree_edges_to_null)
    return get_plot_div(g)

layout_fns = {
    'circular' : nx.circular_layout,
    'kk' : nx.kamada_kawai_layout,
    'random' : nx.random_layout,
    'shell' : nx.shell_layout,
    'spectral' : nx.spectral_layout,
    'spring' : nx.spring_layout,
}

def iplot_model(m, graph_layout = 'spring', draw_tree_edges_to_null = False):
    offline.iplot(model_to_fig(m, graph_layout, draw_tree_edges_to_null = draw_tree_edges_to_null))

def model_to_fig(m, graph_layout = 'spring', draw_tree_edges_to_null = False):
    g = model_to_nx_graph(m, draw_tree_edges_to_null = draw_tree_edges_to_null)
    return nx_graph_to_plotly_fig(g, graph_layout)

def model_to_nx_graph(m, draw_tree_edges_to_null = False):
    if isinstance(m, graph.Graph):
        gm = m
    else:
        gm = checks.graph_from_smt_model(m, with_tree_edges_to_null = draw_tree_edges_to_null)

    var_dict = {v : [] for v in gm.val}
    for x, v in gm.s.items():
        var_dict[v].append(x)

    g = nx.DiGraph()
    for v in gm.val:
        data = gm.succ_of(v, consts.FLD_DATA)
        if data is not None:
            labels = [str(data)]
        else:
            labels = []
        xs = var_dict[v]
        if xs:
            labels.append(' '.join(xs))
        label = ' / '.join(labels)
        g.add_node(v, label=label)
    for (src,lbl), trg in gm.ptr.items():
        if lbl != consts.FLD_DATA:
            g.add_edge(src, trg, label=lbl)
    return g

def get_plot_div(g, graph_layout = 'spring'):
    return offline.plot(nx_graph_to_plotly_fig(g, graph_layout),
                        show_link = False,
                        auto_open = False,
                        include_plotlyjs = False,
                        output_type = 'div')

def nx_graph_to_plotly_fig(g, graph_layout = 'spring'):
    layout_fn = layout_fns[graph_layout]
    pos = layout_fn(g)
    #print(pos)
    x_nodes = [pos[k][0] for k in g.nodes()]
    y_nodes = [pos[k][1] for k in g.nodes()]
    labels = [g.node[k]['label'] for k in g.nodes()]

    ptr_labels = set()
    x_src_edges = {}
    y_src_edges = {}
    x_trg_edges = {}
    y_trg_edges = {}

    def add_edge(label, from_, to, is_src_edge):
        ptr_labels.add(label)
        if is_src_edge:
            x_dict, y_dict = x_src_edges, y_src_edges
        else:
            x_dict, y_dict = x_trg_edges, y_trg_edges
        x_dict.setdefault(label, []).extend([from_[0], to[0], None])
        y_dict.setdefault(label, []).extend([from_[1], to[1], None])

    for edge in g.edges():
        src, trg = edge[0], edge[1]
        src_pos = [pos[src][i] for i in (0,1)]
        trg_pos = [pos[trg][i] for i in (0,1)]
        mid_pos = [(pos[src][i] + (pos[trg][i] - pos[src][i]) * 3 / 4) for i in (0,1)]
        add_edge(g[src][trg]['label'], src_pos, mid_pos, True)
        add_edge(g[src][trg]['label'], mid_pos, trg_pos, False)

    colors = ['red','green','blue','orange']

    edge_traces = []
    for i,lbl in enumerate(ptr_labels):
        col = colors[i]
        edge_traces.extend([
            go.Scatter(x=x_src_edges[lbl],
                       y=y_src_edges[lbl],
                       mode='lines+text',
                       text=lbl,
                       textposition='top',
                       line=go.Line(color=col, width=2),
                       hoverinfo='none'
            ),
           go.Scatter(x=x_trg_edges[lbl],
                      y=y_trg_edges[lbl],
                      mode='lines',
                      line=go.Line(color=col, width=7),
                      hoverinfo='none'
            )
        ])

    vertex_trace=go.Scatter(x=x_nodes,
                            y=y_nodes,
                            mode='markers+text',
                            marker=go.Marker(symbol='dot',
                                             size=25,
                                             color='rgb(127,127,255)',
                                             line=go.Line(color='rgb(50,50,50)', width=2)
                            ),
                            text=labels,
                            textposition='top',
                            hoverinfo='text'
    )

    data=go.Data([*edge_traces, vertex_trace])

    layout=go.Layout(title=g.graph.get('title', 'Model'),
                     font=go.Font(size=12),
                     showlegend=False,
                     xaxis=go.XAxis(showgrid=False, zeroline=False, showticklabels=False),
                     yaxis=go.YAxis(showgrid=False, zeroline=False, showticklabels=False),
                     hovermode='closest'
    )

    fig=go.Figure(data=data,
                 layout=layout)
    #print(fig)
    return fig

if __name__ == '__main__':
    N = 10
    g = nx.DiGraph()
    for i in range(N-1):
        g.add_edge(i, i+1)
        if i < N / 2:
            g.add_edge(i, 2*i)
    labels = [str(i) for i in range(N)]
    print(plot_nx_graph(g, labels))
