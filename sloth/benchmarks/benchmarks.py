# coding: utf-8

import sys
import traceback

from .. import api, config, consts, wrapper, z3api
from ..model import model
from ..utils import timing, utils
from . import defaults

SUCCESS = None
BENCHMARK_BOUND = 20
SKIP_BUGS = True
# TODO: Maybe allow encoding some expectations as comments in the benchmark files, e.g. about the minimum number of locations?

def _configure_and_execute(file, encoder):
    # Reset z3
    z3api.Solver().reset()
    # TODO: Set loglevel to error
    io_config = config.IOConfig()
    io_config.input_file = file
    io_config.show_result = False
    io_config.print_stats = False
    io_config.propagate_all_exceptions = True
    solver_config = config.SolverConfig()
    #solver_config.override_bound = BENCHMARK_BOUND
    solver_config.encoder = encoder
    solver_config.structs = api.sl.structs
    print("Will now run solver on " + file)
    return wrapper.run(io_config, solver_config, batch_mode = True)

def run_benchmark(b, backend):
    """Runs the benchmark in the file of the given name.

    Semantics based on the filename: The benchmark will be considered successful if

    - b contains the string "error" and an exception is thrown during execution
    - b contains the string "unsat" and no solution is found
    - b contains the string "broken" (indicating a known bug/missing feature in the solver)
    - b contains none of the above strings and the solver finds a model

    """
    ERROR = (b,backend)

    expect_error = consts.BM_EXPECT_ERROR in b
    expect_unsat = consts.BM_EXPECT_UNSAT in b
    known_bug = consts.BM_EXPECT_BUG in b
    if expect_error: msg = "FAILURE"
    elif expect_unsat: msg = "UNSAT"
    else: msg = "SUCCESS"

    def handle_err(msg):
        print("ERROR: " + msg)
        if known_bug:
            print("NOTE: This is a known bug, not considering this a failure")
            timing.log(timing.EventType.Mark, mark="(*)")
        else:
            timing.log(timing.EventType.Mark, mark="*")

    print("Running {} on backend {} expecting {}".format(b, backend, msg))
    try:
        #with utils.nostdout():
            res = _configure_and_execute(b, backend)
    except Exception as e:
        print("Exception: " + repr(e))
        if not expect_error:
            handle_err("Benchmark {} should not have caused an exception".format(b))
            traceback.print_exc()
        return SUCCESS if expect_error or known_bug else ERROR
    else:
        if res is not None:
            print("Found model with locations {}".format(list(res.locs())))
        if expect_error:
            handle_err("Benchmark {} should have failed".format(b))
            return SUCESS if known_bug else ERROR
        elif expect_unsat and res is not None:
            handle_err("Got model for unsatisfiable benchmark {}".format(b))
        elif (not expect_unsat) and res is None:
            handle_err("Did not find model for satisfiable benchmark {}".format(b))
        return SUCCESS if ((res is None) == expect_unsat) or known_bug else ERROR

if __name__ == "__main__":
    if len(sys.argv) > 1:
        dir_whitelist = sys.argv[1:]
        fmt = "Will only run benchmarks in the following subfolders of {}: {}"
        print(fmt.format(config.BENCHMARK_PATH, ", ".join(dir_whitelist)))
    else:
        print("Will run all benchmarks in " + config.BENCHMARK_PATH)
        dir_whitelist = None

    benchmarks = utils.collect_smt2_files(config.BENCHMARK_PATH, dir_whitelist)
    results = [run_benchmark(b, encoder)
               for b in benchmarks
               for encoder in [config.EncoderEnum.Direct]
               #for encoder in [config.EncoderEnum.Exponential]
               #for encoder in [config.EncoderEnum.Direct, config.EncoderEnum.Exponential]
               if not SKIP_BUGS or consts.BM_EXPECT_BUG not in b]
    errs = tuple(filter(lambda b : b is not None, results))
    num_errs = len(errs)

    timing.print_solver_stats()
    print("Passed {}/{} benchmarks".format(len(results) - len(errs), len(results)))
    #print("Limit for unfolding depth used: {}".format(BENCHMARK_BOUND))

    if num_errs > 0:
        print("Failed benchmarks: {}".format(errs))
        raise Exception("Benchmark suite failed")
