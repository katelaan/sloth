import os
import argparse

from . import consts, config
from .backend import backends, struct
from .utils import logger

def arg_parser():
    # TODO: Allow timelimit?
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", type = str,
                        help = "Path to SMT2 encoding of the SL formula")
    # TODO: Indicate the possible values in the summary
    parser.add_argument("-b", "--backend", type = str, default = consts.LAMBDA_BACKEND)
    parser.add_argument("-d", "--max-depth",
                        type = int, default = config.MAX_DEPTH,
                        help = "depth bound for model search")
    parser.add_argument("-p", "--plot",
                        help = "plot model; requires igraph + pycairo",
                        action = "store_true")
    parser.add_argument("--no-isolated-nodes",
                        help = "do not plot locations w/o (non-default) edges",
                        action = "store_true")
    parser.add_argument("--dump-smt",
                        help = "write smt encoding to file",
                        action = "store_true")
    parser.add_argument("--dump-til-depth", type = int, default = 0,
                        help = "dump all encodings up to the given unfolding depth")
    parser.add_argument("--force-depth",
                        help = "force structures of exact depth",
                        action = "store_true")
    # TODO: Implement this? (I.e., start from encoding.smt2, thus doing just model computation + plotting rather than encoding)
    #parser.add_argument("--from-encoding", help = "skip parsing")
    parser.add_argument("-v", "--verbose", help = "increase output verbosity",
                        action = "store_true")
    parser.add_argument("-q", "--quiet", help = "decrease output verbosity",
                        action = "store_true")
    parser.add_argument("--debug", help = "debug output",
                        action = "store_true")

    parser.add_argument("--symbol-table",
                        help = "Show SL symbols that can be used in the input files",
                        #, help = argparse.SUPPRESS,
                        action = "store_true")
    parser.add_argument("--suppress-result",
                        help = argparse.SUPPRESS,
                        action = "store_true")

    return parser

def _initialize_z3():
    # Check if we can import + initialize z3 & print error message otherwise
    try:
        import z3
    except:
        try:
            user_paths = os.environ['PYTHONPATH']
        except KeyError:
            user_paths = ""
        print("Can't find z3 python interface in path, will exit")
        print("Current $PYTHONPATH: " + user_paths)
        return False
    else:
        return True

def _configure_logger(verbose, quiet):
    if verbose:
        level=logger.DEBUG
    elif quiet:
        level=logger.WARN
    else:
        level=logger.INFO
    logger.set_level(level)
    #logger.basicConfig(format='%(asctime)s [%(filename)s:%(lineno)d]: %(message)s', level=level)

def _configure_io(args):
    io_config = config.IOConfig()
    io_config.input_file = args.filename
    io_config.dump_smt = args.dump_smt
    io_config.dump_til_depth = args.dump_til_depth
    io_config.show_result = not args.suppress_result
    io_config.plot = args.plot
    io_config.plot_isolated_nodes = not args.no_isolated_nodes
    io_config.print_symbol_table = args.symbol_table
    if args.debug:
        io_config.propagate_all_exceptions = True
        config.debug = True
    return io_config

def _configure_solver(args):
    from .backend import symbols
    solver_config = config.SolverConfig()
    solver_config.max_depth = args.max_depth
    solver_config.force_depth = args.force_depth
    solver_config.backend = args.backend
    if backends.exists(solver_config.backend):
        backend = backends.get(solver_config.backend)
        logger.info("Backend: {}".format(backend))
        solver_config.structs = struct.make_predef_structs(
            # Configure the backend for generating the SMT encoding
            encoder_backend = backend
        )
        return solver_config
    else:
        logger.error("Unknown backend '{}' => Terminating".format(solver_config.backend))
        return None

if __name__ == "__main__":
    parser = arg_parser()
    args = parser.parse_args()
    _configure_logger(args.verbose, args.quiet)

    if _initialize_z3():
        from . import wrapper
        io_config = _configure_io(args)
        solver_config = _configure_solver(args)
        if solver_config is not None:
            wrapper.run(io_config, solver_config)
