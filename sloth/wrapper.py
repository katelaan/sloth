"""Provides high-level access to the solver via the :func:`run` function.
"""

from . import config
from . import slparser, serialization
from .backend import struct
from .encoder import strategy
from .model import model
from .utils import logger, timing, utils

###############################################################################
# IO Routines for Preprocessing and Postprocessing
###############################################################################

def parse_sl(input_file, structs):
    """Parses the file of the given name into an expression reference."""
    try:
        with open(input_file, "r") as f:
            content = f.read()
    except FileNotFoundError:
        print(input_file + " does not exist")
        return None
    else:
        return slparser.parse_sl(content, structs)

def show_result(model, structs):
    """Print information/statistics about the model"""
    print("Model: {}".format(model))
    loc_counts = ("|{}|={}".format(s.predicate(), len(model.struct_model(s)))
                  for s in model.structs
                  if bool(model.struct_model(s)))
    print("Sort cardinalities: {}".format(', '.join(loc_counts)))
    print("Variables/constants per sort:")
    for s in model.structs:
        if bool(model.struct_model(s)):
            print("  {}: {}".format(s.name, model.struct_model(s).loc_consts()))
            #print("  {}: {}".format(s.name, model.struct_model(s).fp_consts()))
    print("Variables/constants by location:")
    sorted_locs = sorted((int(str(k.loc)), v) for (k,v) in model.node_labeling.items())
    for k,v in sorted_locs:
        if v:
            print("  {}: {}".format(k, v))
    # for key in model.node_labeling:
    #     if model.node_labeling[key]:
    #         print("  {}: {}".format(key.loc, model.node_labeling[key]))

def plot_result(model, draw_isolated_nodes = True):
    """Plot the given model using igraph"""
    try:
        # Import down here so that the tool works without igraph
        # (if plotting is disabled)
        from .model import plotter
    except ImportError as e:
        print("Could not initialize model plotting: " + str(e))
        print("Have you installed pycairo and python-igraph?")
    else:
        plotter.plot_model(model, draw_isolated_nodes)

def dump_encodings(io_config, solver_config, parsed, result_encoding):
    """Write SMT encoding(s) to file.

    Depending on the `io_config`, saves either the last SMT encoding
    or all encodings up to the configured depth bound.

    """
    depth = io_config.dump_til_depth
    force_depth = solver_config.force_depth
    structs = solver_config.structs

    assert(depth >= 0)
    if depth == 0:
        file = config.ENCODING_FILE_PREFIX + ".smt2"
        logger.info("Writing SMTLIB2 encoding to file {}".format(file))
        serialization.write_encoding_to_file(file, result_encoding, structs)
    else:
        logger.info("Will write all unfoldings up to depth {} to files {}*.smt2".format(depth, config.ENCODING_FILE_PREFIX))
        raise NotImplementedError("Dumping of all encodings no longer supported")

###############################################################################
# Main solution process
###############################################################################

def preprocess(io_config, solver_config):
    """Encapsulates the parsing process, possibly producing debug output.

    Whether debug output is produced depends on the `io_config`."""
    if io_config.print_symbol_table:
        struct.print_sl_summary(solver_config.structs)
    logger.info("Will solve SL query in '{}'".format(io_config.input_file))
    parsed, max_depth = parse_sl(io_config.input_file, solver_config.structs)
    if parsed is not None:
        logger.debug("Parse result:\n".format(parsed))
    else:
        raise utils.SlothException("Parser error")
    if max_depth is not None:
        print("Found depth bound in input file: {}".format(max_depth))
        print("Will restrict max depth to {}".format(max_depth))
        solver_config.max_depth = max_depth
    return parsed

def solve(solver_config, parsed):
    """Encapsulates the solution process."""
    if parsed is not None:
        result_state = strategy.decide(solver_config.structs,
                                       parsed,
                                       solver_config.max_depth)
        if not result_state.is_success():
            print("Could NOT prove satisfiability")
            return None
        else:
            return result_state
    else:
        return None

def postprocess(io_config, solver_config, parsed, result_state):
    """Encapsulates all tasks to be executed after the solver has finished.

    Depending on the `io_config`, this may include dumping encodings
    to file, showing a textual representation of the model or plotting
    the model.

    """
    if io_config.dump_smt:
        # Dump SMT encodings regardless of success
        dump_encodings(io_config, solver_config, parsed, result_state.encoding)
    if result_state and result_state.model is not None:
        adapter = result_state.model
        # Print and/or plot model in case of success
        if io_config.show_result:
            show_result(adapter, solver_config.structs)
        if io_config.plot:
            plot_result(adapter, io_config.plot_isolated_nodes)
        return adapter

def _handle_exception(io_config, e):
    if io_config.propagate_all_exceptions:
        import traceback
        traceback.print_exc()
        raise e
    else:
        print("Terminating with exception ({})".format(e))

def run(io_config, solver_config, batch_mode = False):
    """Run the solver according to the given configuration.

    In batch mode, the result is returned for further processing."""
    timing.log(
        timing.EventType.Start,
        benchmark = io_config.input_file,
        backend = solver_config.backend
    )
    try:
        parsed = preprocess(io_config, solver_config)
    except Exception as e:
        parsed = None
        timing.log(timing.EventType.Error)
        _handle_exception(io_config, e)

    if parsed is not None:
        try:
            result = solve(solver_config, parsed)
        except Exception as e:
            result = None
            timing.log(timing.EventType.Error)
            _handle_exception(io_config, e)
        else:
            if result is None:
                timing.log(timing.EventType.Unsat)
            else:
                timing.log(timing.EventType.Sat)
            adapter = postprocess(io_config, solver_config, parsed, result)

    if io_config.print_stats:
        timing.print_solver_stats()

    if batch_mode:
        return adapter
