import math

import networkx as nx
import plotly.offline as offline
import plotly.graph_objs as go

from .. import consts
from . import checks
from . import forestlayout
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
    g, pos = nx_graph_and_layout(m,
                                 graph_layout = graph_layout,
                                 draw_tree_edges_to_null = draw_tree_edges_to_null)
    return get_plot_div(g, pos)

def iplot_model(m, graph_layout = 'forest', draw_tree_edges_to_null = False):
    offline.iplot(model_to_fig(m, graph_layout, draw_tree_edges_to_null = draw_tree_edges_to_null))

def model_to_fig(m, graph_layout = 'forest', draw_tree_edges_to_null = False):
    g, pos = nx_graph_and_layout(m,
                                 graph_layout = graph_layout,
                                 draw_tree_edges_to_null = draw_tree_edges_to_null)
    return nx_graph_to_plotly_fig(g, pos)

def nx_graph_and_layout(m, graph_layout = 'forest', draw_tree_edges_to_null = False):
    if not isinstance(m, graph.Graph):
        m = checks.graph_from_smt_model(m, with_tree_edges_to_null = draw_tree_edges_to_null)
    g = model_to_nx_graph(m, draw_tree_edges_to_null = draw_tree_edges_to_null)
    pos = resolve_layout(graph_layout, m, g)
    return g, pos

def model_to_nx_graph(gm, draw_tree_edges_to_null = False):
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

def get_plot_div(g, pos):
    return offline.plot(nx_graph_to_plotly_fig(g, pos),
                        show_link = False,
                        auto_open = False,
                        include_plotlyjs = False,
                        output_type = 'div')

layout_fns = {
    'circular' : nx.circular_layout,
    'forest' : None,
    'kk' : nx.kamada_kawai_layout,
    'random' : nx.random_layout,
    'shell' : nx.shell_layout,
    'spectral' : nx.spectral_layout,
    'spring' : nx.spring_layout,
}

def resolve_layout(graph_layout, gm, g):
    assert isinstance(gm, graph.Graph)
    assert isinstance(g, nx.DiGraph)
    if graph_layout == 'forest':
        return forestlayout.layout(gm)
    else:
        layout_fn = layout_fns[graph_layout]
        return layout_fn(g)

def nx_graph_to_plotly_fig(g, pos):
    #print(pos)
    x_nodes = [pos[k][0] for k in g.nodes()]
    y_nodes = [pos[k][1] for k in g.nodes()]
    labels = [g.node[k]['label'] for k in g.nodes()]

    edge_traces = []
    colors = ['red','green','blue','orange']
    ptr_labels = ['left', 'right', 'next']

    for num, lbl in enumerate(ptr_labels):

        x_src_edges = []
        y_src_edges = []
        x_trg_edges = []
        y_trg_edges = []

        if lbl == 'right':
            offset_factor = -1
        else:
            offset_factor = 1

        def add_edge(from_, to, is_src_edge):
            if is_src_edge:
                x_ls, y_ls = x_src_edges, y_src_edges
            else:
                x_ls, y_ls = x_trg_edges, y_trg_edges
            x_ls.extend([from_[0], to[0], None])
            y_ls.extend([from_[1], to[1], None])
            #print('Added edge from {} to {}'.format(from_, to))

        # Compute edge positions
        for edge in g.edges():
            src, trg = edge[0], edge[1]
            if g[src][trg]['label'] != lbl:
                continue

            src_pos = [pos[src][i] for i in (0,1)]
            trg_pos = [pos[trg][i] for i in (0,1)]

            diff_x = trg_pos[0] - src_pos[0]
            diff_y = trg_pos[1] - src_pos[1]
            normal_vec = [diff_y, - diff_x]
            #print('src={}, trg={}, src_pos={}, trg_pos={}, diff={}, {}, normal_vec = {}'.format(src, trg, src_pos, trg_pos, diff_x, diff_y, normal_vec))

            offset_step = 0.05
            num_frags = 64

            for i in range(num_frags):
                src_num_steps = min(num_frags - i, i)
                trg_num_steps = min(num_frags - (i + 1), i + 1)
                src_offset = offset_factor * offset_step * math.sin(src_num_steps / num_frags * math.pi )
                trg_offset = offset_factor * offset_step * math.sin(trg_num_steps / num_frags * math.pi )

                src_pos = [pos[src][j] + ((pos[trg][j] - pos[src][j]) * i / num_frags)
                           + src_offset * normal_vec[j]
                           for j in (0,1)]
                trg_pos = [pos[src][j] + ((pos[trg][j] - pos[src][j]) * (i+1) / num_frags)
                           + trg_offset * normal_vec[j]
                           for j in (0,1)]
                is_src_edge = i < num_frags * 3 / 4
                add_edge(src_pos, trg_pos, is_src_edge)

        # Create edge traces
        col = colors[num]

        edge_traces.extend([
            go.Scatter(x=x_src_edges,
                       y=y_src_edges,
                       mode='lines',
                       name=lbl,
                       textposition='top',
                       line=go.Line(color=col, width=2),
                       hoverinfo='none',
                       showlegend=True
            ),
           go.Scatter(x=x_trg_edges,
                      y=y_trg_edges,
                      mode='lines',
                      line=go.Line(color=col, width=7),
                      showlegend=False,
                      hoverinfo='none'
            )
        ])

    vertex_trace=go.Scatter(x=x_nodes,
                            y=y_nodes,
                            mode='markers+text',
                            marker=go.Marker(symbol='dot',
                                             size=18,
                                             color='rgb(127,127,255)',
                                             line=go.Line(color='rgb(50,50,50)', width=2)
                            ),
                            text=labels,
                            showlegend=False,
                            textposition='top',
                            hoverinfo='text'
    )

    data=go.Data([*edge_traces, vertex_trace])

    layout=go.Layout(title=g.graph.get('title', 'Model'),
                     font=go.Font(size=12),
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
