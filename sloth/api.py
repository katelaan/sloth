"""The top-level API for interacting with the separation logic solver.

.. testsetup::

  from sloth.api import *

TODO: Remove the quantified backend from the public API? The
polynomial encoding (which is used by the API now) is only available
for the lambda backend.

By default, the lambda backend is active. You can switch back and forth at any time:

>>> backend
Integer locations & lambdas
>>> activate_quantified_backend()
Backend: Uninterpreted sorts & universal quantification.
>>> activate_lambda_backend()
Backend: Integer locations & lambdas.

You can either parse input or build input expressions by hand:

>>> parse('../benchmarks/list-symbolic-heaps/list.smt2')
ParseResult(expr=sl.list(a), backend=Integer locations & lambdas)
>>> sl.list('a')
sl.list(a)

See the documentation of :class:`sloth.slapi.SlApi` for more examples of
manually built expressions.

Given a parse result or an expression, you can run encoding, solving,
model generation, etc.

>>> is_sat(sl.list('a'))
True
>>> encoding = encode(sl.list.pointsto('a', 'b'))
>>> encoding.to_z3_expr() # doctest: +ELLIPSIS
And(...)
>>> is_sat_encoding(encoding)
True
>>> model(encoding) # doctest: +ELLIPSIS
Model [...]
>>> stats(model(encoding)) # doctest: +ELLIPSIS
Model: ...
>>> solve(sl.list('a'))
Model [...]

In addition there are various methods to help you find and interact with benchmarks:

>>> all_benchmarks() # doctest: +ELLIPSIS
['../benchmarks/...]
>>> find_benchmarks('list', 'seg') # doctest: +ELLIPSIS
['../benchmarks/list-boolean-closure/list-not-list-segs.smt2', '../benchmarks/list-boolean-closure/unsat-list-segs-not-list.smt2', ...]
>>> benchmark('contains', '1234.smt2')
'../benchmarks/tree-data/tree-contains1234.smt2'

"""

# TODO: Encoding up to certain rewriting pass / running individual passes?

import collections, os

import z3

from . import config, consts
from . import slparser, wrapper, slapi
from . import z3api
from .backend import LambdaBackend, QuantifiedBackend, struct
from .encoder import encoder, constraints
from .model import model as model_module, checks, graph, plotter
from .utils import logger, utils
from .z3api import z3utils

class ApiException(utils.SlothException):
    """Raised when the API is used in an unintended way."""

NO_MODEL_AVAILABLE = 'Unsatisfiable => no model available'

###############################################################################
# Backend activation / management
###############################################################################

backend = None
sl = None

def _activation_msg(backend):
    print("Backend: {}.".format(backend))

def _activate_backend(b, print_activation_msg):
    global backend
    global sl
    backend = b
    sl = slapi.SlApi(backend)
    if print_activation_msg:
        _activation_msg(backend)

def activate_lambda_backend(print_activation_msg = True):
    """Activates the lambda backend."""
    _activate_backend(LambdaBackend, print_activation_msg)

def activate_quantified_backend(msg = True):
    """Activates the backend with unintepreted sorts & quantifiers."""
    _activate_backend(QuantifiedBackend, msg)

# By default, activate the lambda backend
activate_lambda_backend(print_activation_msg = False)

###############################################################################
# Parsing
###############################################################################

ParseResult = collections.namedtuple("ParseResult", "expr backend")

def parse(string):
    """Parses the given string or file.

    :param: string: Either a string in our extended SMTLIB format or the name of a file containing such a string.

    :rtype: :class:`ParseResult`"""
    if '\n' not in string:
        # Single line => Probably filename
        parsed = slparser.parse_sl_file(string, sl.structs)
    else:
        parsed = slparser.parse_sl(string, sl.structs)[0]
    return ParseResult(parsed, backend)

def _ensure_parsed(input):
    if isinstance(input, encoder.slast.SlAst):
        return ParseResult(input, backend)
    if isinstance(input, z3.ExprRef):
        return ParseResult(input, backend)
    elif isinstance(input, ParseResult):
        return input
    elif isinstance(input, str):
        # Single line => Probably file name
        return parse(input)
    elif isinstance(input, constraints.Z3Input):
        msg = "Received encoding instead of parser input or parse result"
        raise ApiException(msg)
    else:
        fmt = "Don't know how to handle parser input {}"
        raise ApiException(fmt.format(input))

def _ensure_correct_backend(parsed):
    if parsed.backend is not backend:
        print("Parse result for different backend => Switching backend.")
        _activate_backend(parsed.backend)

###############################################################################
# Encoding
###############################################################################

def _default_depth(depth):
    if depth == None:
        print("Defaulting to depth 0")
        return 0
    else:
        return depth

def encode(input, override_bound = None):
    """Encodes the given input assuming uniform depth `depth`.

    Begins by parsing the input if necessary.
    If no `depth` is provided, depth 0 is assumed by default.

    :param: input: Filename, SMTLIB string or parse result to be encoded.
    :param: depth: `int` specifying the unfolding depth in the encoding.

    :rtype: :class:`constraints.Z3Input`

    """
    parsed = _ensure_parsed(input)
    _ensure_correct_backend(parsed)
    return encoder.encode_sl_expr(sl, parsed.expr, override_bound)

###############################################################################
# Solving
###############################################################################

def is_sat_encoding(encoding):
    """Return True iff the given encoding is satisfiable."""
    assert isinstance(encoding, constraints.Z3Input), utils.wrong_type(encoding)
    return z3api.is_sat(encoding.to_z3_expr())

def is_sat(input, override_bound = None):
    """Return True iff `input` is satisfiable.

    :param: input: Input to solve (either filename, SMTLIB string or :class:`ParseResult`)
    :param: override_bound: Manual override for the size bound of the model

    """
    e = encode(input, override_bound)
    return z3api.is_sat(e.to_z3_expr())

def solve(input, override_bound = None):
    """Compute :class:`model.SmtModel` for the given `input`.

    :param: input: Input to solve (either filename, SMTLIB string or :class:`ParseResult`)
    :param: override_bound: Manual override for the size bound of the model

    :rtype: :class:`model.SmtModel`

    """
    e = encode(input, override_bound)
    if z3api.is_sat(e.to_z3_expr()):
        return e.label_model(z3api.model())
    else:
        print(NO_MODEL_AVAILABLE)
        return None

def show_evaluation_steps(input, export_file = None, override_bound = None):
    """Show the encoding as well as all types of model computed for the given input."""
    e = encode(input, override_bound)
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
        g = checks.canonical_graph(a)
        print(g)
        print('\nGraph repr:\n-----------')
        print(repr(g))
        print('\nPointers by var:\n----------------')
        print('\n'.join(g.all_named_ptrs_str()))


###############################################################################
# Model adaptation & plotting
###############################################################################

def current_model(consts, structs):
    try:
        return model_module.SmtModel(z3api.model(),
                                     consts,
                                     structs)
    except z3.Z3Exception as e:
        return None

def model(input, override_bound = None):
    """Returns model for the given expression or encoding.

    Raises :class:`ApiException` if no model is available.

    :param: encoding: :class:`constraints.Z3Input` instance to encode

    :rtype: :class:`model.SmtModel`

    """
    if isinstance(input, constraints.Z3Input):
        if is_sat_encoding(input):
            return current_model(input.all_consts(), input.structs)
        print(NO_MODEL_AVAILABLE)
        return None
    else:
        return solve(input, override_bound)

def evaluate_to_graph(input, ignore_null = False, with_tree_edges_to_null = False, override_bound = None):
    """
    >>> x, y, z = sl.list.locs('x y z'); sl_expr = sl.sepcon(sl.list.pointsto(x, y), sl.list.pointsto(y, z), sl.list.pointsto(z, sl.list.null))
    >>> evaluate_to_graph(sl_expr)
    Graph({0, 1, 2, 3}, {(0, 'next'): 1, (1, 'next'): 2, (2, 'next'): 3}, {'sl.list.null': 3, 'x': 0, 'y': 1, 'z': 2})

    """
    m = solve(input, override_bound)
    return model_to_graph(m, ignore_null = ignore_null, with_tree_edges_to_null = with_tree_edges_to_null)

def z3_to_py(expr):
    """Converts given z3 literal into python's built-in numbers."""
    if not isinstance(expr, z3.IntNumRef):
        raise ApiException("Can only convert convert integer literals to python")
    else:
        return expr.as_long()

def model_to_graph(model, ignore_null = False, with_tree_edges_to_null = False):
    return checks.graph_from_smt_model(model, ignore_null = ignore_null, with_tree_edges_to_null = with_tree_edges_to_null)

def stats(mod = None):
    """Print statistics about the given :class:`model.SmtModel`."""
    if mod is None: mod = model()
    if isinstance(mod, model_module.SmtModel):
        wrapper.show_result(mod, sl.structs)
    else:
        raise ApiException("Can only show stats for SmtModel")

iplot_initialized = False

def iplot(mod, layout = None, draw_tree_edges_to_null = False):
    global iplot_initialized
    if not iplot_initialized:
        from plotly.offline import init_notebook_mode
        init_notebook_mode(connected=True)
        iplot_initialized = True

    if isinstance(mod, model_module.SmtModel) or isinstance(mod, graph.Graph):
        if layout is not None:
            plotter.iplot_model(mod, graph_layout = layout, draw_tree_edges_to_null = draw_tree_edges_to_null)
        else:
            plotter.iplot_model(mod, draw_tree_edges_to_null = draw_tree_edges_to_null)
    else:
        raise ApiException("Cannot plot {}".format(type(mod).__name__))

def plot(mod, filename = 'plot.html'):
    """Plot the given :class:`model.SmtModel`."""
    if isinstance(mod, model_module.SmtModel) or isinstance(mod, graph.Graph):
        plotter.models_to_html([mod], filename = filename)
        print ('Saved plot in {}'.format(filename))
    else:
        raise ApiException("Cannot plot {}".format(type(mod).__name__))

###############################################################################
# Benchmarking and testing API
###############################################################################

def print_both_encodings(b, depth):
    global backend
    backup = backend
    activate_lambda_backend(suppress_warning = True)
    print(encode(b, 0))
    activate_quantified_backend(suppress_warning = True)
    print(encode(b, 0))
    backend = backup

def timed(f):
    # TODO: Implement timing
    return f()

def all_benchmarks():
    # To make doctests work
    path = config.BENCHMARK_PATH
    if os.getcwd().endswith("/docs"):
        path = "../" + path
    return utils.collect_smt2_files(path)

def find_benchmarks(*substrings):
    return [bm for bm in all_benchmarks() if utils.contains_all(substrings, bm)]

def benchmark(*substrings):
    matches = find_benchmarks(*substrings)
    if len(matches) == 1:
        return matches[0]
    else:
        fmt = "No unique match for substrings {}: Found {}"
        raise ApiException(fmt.format(substrings, matches))

def parseable_benchmarks():
    for bm in all_benchmarks():
        if not consts.BM_EXPECT_ERROR in bm:
            yield bm

def cat(filename):
    with open(filename, "r") as f:
        return f.read()

def show(filename):
    print(cat(filename))

def verbose():
    logger.set_level(logger.INFO)

def vverbose():
    logger.set_level(logger.DEBUG)

def quiet():
    logger.set_level(logger.WARN)
