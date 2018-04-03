import logging

from . import consts

debug = False

# If the tool crashes with
# > Z3Exception("init(Z3_LIBRARY_PATH) must be invoked before using Z3-python"),
# you can manually set the path to libz3.so below
Z3_LIB_PATH = ""

# Path / file config
BENCHMARK_PATH = "benchmarks"
ENCODING_FILE_PREFIX = "encoding"

# Solver config
MAX_DEPTH = 2 ** 15
MAX_NUM_STOPS = 2
MAX_BRANCHING = 2

def max_num_stops(struct):
    if struct.is_linear():
        return 1
    else:
        return MAX_NUM_STOPS

DEFAULT_LOG_LEVEL = logging.WARN

class IOConfig:

    def __init__(self):
        self.input_file = None
        self.print_symbol_table = False
        self.dump_smt = False
        self.dump_til_depth = 0
        self.show_result = True
        self.plot = False
        self.plot_isolated_nodes = True
        self.encoding_file = ENCODING_FILE_PREFIX + ".smt2"
        self.print_stats = True
        self.propagate_all_exceptions = False

    def indexed_encoding_file(self, i):
        return self.encoding_file[:-5] + str(i) + self.encoding_file[-5:]

class SolverConfig:

    def __init__(self):
        self.max_depth = MAX_DEPTH
        self.force_depth = False
        self.max_num_stops = MAX_NUM_STOPS
        self.backend = consts.QUANTIFIED_BACKEND
        self.structs = []

    def print_config(self):
        print(self.__args__)
