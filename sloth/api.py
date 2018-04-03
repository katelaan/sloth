"""The top-level API for interacting with the separation logic solver.

.. testsetup::

  from sloth.api import *

By default, the lambda backend is active. You can switch back and forth at any time:

>>> backend
Integer locations & lambdas
>>> activate_quantified_backend()
Backend: Uninterpreted sorts & universal quantification.
>>> activate_lambda_backend()
Backend: Integer locations & lambdas.

You can either parse input or build input expressions by hand:

>>> parse("../benchmarks/list-symbolic-heaps/list.smt2")
ParseResult(expr=sl.list(a), backend=Integer locations & lambdas)
>>> sl.list("a")
sl.list(a)

See the documentation of :class:`sloth.slapi.SlApi` for more examples of
manually built expressions.

Given a parse result or an expression, you can run encoding, solving,
model generation, etc.

>>> is_sat(sl.list("a"))
True
>>> encoding = encode(sl.list.pointsto("a","b"))
Defaulting to depth 0
>>> encoding.full() # doctest: +ELLIPSIS
And(...)
>>> is_sat_encoding(encoding)
True
>>> model(encoding) # doctest: +ELLIPSIS
Model [...]
>>> stats(model(encoding)) # doctest: +ELLIPSIS
Model: ...
>>> solve(sl.list("a"))
Model [...]

In addition there are various methods to help you find and interact with benchmarks:

>>> all_benchmarks() # doctest: +ELLIPSIS
['../benchmarks/...]
>>> find_benchmarks("list", "seg")
['../benchmarks/list-boolean-closure/list-not-list-segs.smt2', '../benchmarks/list-boolean-closure/unsat-list-segs-not-list.smt2', '../benchmarks/list-symbolic-heaps/list-sixteen-segments.smt2']
>>> benchmark("unsat", "list", "seg")
'../benchmarks/list-boolean-closure/unsat-list-segs-not-list.smt2'

Assuming there is just one benchmark whose filename contains both
"list" and "seg", the previous two function calls will return a
singleton list with the filename and the filename, respectively.

"""

# TODO: Encoding up to certain rewriting pass / running individual passes?

import collections, os

import z3

from . import config, consts
from . import slparser, wrapper, slapi
from . import z3api
from .backend import LambdaBackend, QuantifiedBackend, struct
from .encoder import encoder, strategy, astbuilder, astutils
from .model import model as model_module
from .utils import logger, utils
from .z3api import z3utils

class ApiException(utils.SlothException):
    """Raised when the API is used in an unintended way."""

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
    if isinstance(input, z3.ExprRef):
        return ParseResult(input, backend)
    elif isinstance(input, ParseResult):
        return input
    elif isinstance(input, str):
        # Single line => Probably file name
        return parse(input)
    elif isinstance(input, encoder.Encoding):
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

def encode(input, depth = None):
    """Encodes the given input assuming uniform depth `depth`.

    Begins by parsing the input if necessary.
    If no `depth` is provided, depth 0 is assumed by default.

    :param: input: Filename, SMTLIB string or parse result to be encoded.
    :param: depth: `int` specifying the unfolding depth in the encoding.

    :rtype: :class:`encoder.Encoding`

    """
    depth = _default_depth(depth)
    parsed = _ensure_parsed(input)
    _ensure_correct_backend(parsed)
    ast = astbuilder.processed_ast(sl.structs, parsed.expr)
    calls = astutils.pred_calls(ast)
    unfolding_dict = strategy.unfold_uniformly_to_exact_depth(calls, depth)
    return encoder.encode_ast(ast, sl.structs)

###############################################################################
# Solving
###############################################################################

def is_sat_encoding(encoding):
    """Return True iff the given encoding is satisfiable."""
    assert(isinstance(encoding, encoder.Encoding))
    return z3api.is_sat(encoding.full())

def is_sat(input, max_depth = config.MAX_DEPTH):
    """Return True iff there is a satisfiable encoding of `input` of depth at most `max_depth`.

    :param: input: Input to solve (either filename, SMTLIB string or :class:`ParseResult`)
    :param: max_depth: Maximal depth to consider in encoding
    """
    return solve(input, max_depth) is not None

def solve(input, max_depth = config.MAX_DEPTH, print_progress = False):
    """Compute :class:`model.SmtModel` for the given `input`.

    Tries uniform-depth encodings of increasing depth until a model is
    found or `max_depth` is exceeded.

    :param: input: Input to solve (either filename, SMTLIB string or :class:`ParseResult`)
    :param: max_depth: Maximal depth to consider in encoding
    :param: print_progress: Print statements about the current search depth

    :rtype: :class:`model.SmtModel`

    """
    parsed = _ensure_parsed(input)
    _ensure_correct_backend(parsed)
    return strategy.solve_by_unfolding_strategy(sl.structs, parsed.expr, external_depth_bound = max_depth, print_result = print_progress)

###############################################################################
# Model adaptation & plotting
###############################################################################

def model(input):
    """Returns model for the given expression or encoding.

    Raises :class:`ApiException` if no model is available.

    :param: encoding: :class:`encoder.Encoding` instance to encode

    :rtype: :class:`model.SmtModel`"""
    if isinstance(input, encoder.Encoding):
        is_sat_encoding(input)
        try:
            return model_module.SmtModel(z3api.model(),
                                         input.constants,
                                         sl.structs)
        except z3.Z3Exception as e:
            raise ApiException("No model available")
    else:
        return solve(input)

def z3_to_py(expr):
    """Converts given z3 literal into python's built-in numbers."""
    if not isinstance(expr, z3.IntNumRef):
        raise ApiException("Can only convert convert integer literals to python")
    else:
        return expr.as_long()


def stats(mod = None):
    """Print statistics about the given :class:`model.SmtModel`."""
    if mod is None: mod = model()
    if isinstance(mod, model_module.SmtModel):
        wrapper.show_result(mod, sl.structs)
    else:
        raise ApiException("Can only show stats for SmtModel")

def plot(mod = None, draw_isolated_nodes = True):
    """Plot the given :class:`model.SmtModel`."""
    if mod is None: mod = model()
    if isinstance(mod, model_module.SmtModel):
        wrapper.plot_result(mod, draw_isolated_nodes)
    else:
        raise ApiException("Can only plot SmtModel")

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

def verbose():
    logger.set_level(logger.INFO)

def vverbose():
    logger.set_level(logger.DEBUG)

def quiet():
    logger.set_level(logger.WARN)

def dump(encoding, file = None):
    pass

###############################################################################
# Test functions
###############################################################################

def _print_error_report(task_desc, e, bm, p):
    import traceback
    print("#"*80)
    print("{}. Benchmark:".format(task_desc))
    print(cat(bm))
    print("Parse result:")
    print(p)
    print("Exception: {}".format(e))
    print("Trace:")
    traceback.print_exc()
    print("#"*80)
    print("#"*80)

def try_encode_all():
    with utils.stats({"success" : "successes", "fail" : "failures"}) as stats:
        for bm in parseable_benchmarks():
            p = parse(bm)
            print(bm)
            try:
                _ = encode(p, 1)
                stats["success"] += [bm]
            except Exception as e:
                _print_error_report("Encoding failed", e, bm, p)
                stats["fail"] += [bm]

def try_run_all(backend = consts.LAMBDA_BACKEND, max_depth = 3):
    events = {"success" : "successes",
              "efail" : "encoding failures",
              "sfail" : "solver failures",
              "wrong" : "unexpected results"}
    with utils.stats(events) as stats:
        for bm in parseable_benchmarks():
            p = parse(bm)
            print(bm)
            try:
                _ = encode(p, 1)
            except Exception as e:
                print("Encoding failed. Aborting.")
                stats["efail"] += [bm]
            else:
                try:
                    m = solve(p, max_depth)
                    if (m is None) == ("unsat" in bm):
                        stats["success"] += [bm]
                    else:
                        stats["wrong"] += [bm]
                except Exception as e:
                    _print_error_report("Solver failed", e, bm, p)
                    stats["sfail"] += [bm]
