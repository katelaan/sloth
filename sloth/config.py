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
MAX_NUM_STOPS = 2
MAX_BRANCHING = 2

def max_num_stops(struct):
    if struct.is_linear():
        return 1
    else:
        return MAX_NUM_STOPS

DEFAULT_LOG_LEVEL = logging.WARN

class EncoderEnum:

    Direct, Exponential = range(2)

    _d = {
        consts.DIRECT_ENCODER: Direct,
        consts.EXPONENTIAL_ENCODER: Exponential
    }

    @staticmethod
    def from_string(s):
        return EncoderEnum._d.get(s.lower(), EncoderEnum.Direct)

    @staticmethod
    def to_string(e):
        return {v: k for k, v in EncoderEnum._d.items()}.get(e, 'UNKNOWN')

class IOConfig:

    def __init__(self):
        self.input_file = None
        self.print_symbol_table = False
        self.dump_smt = False
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
        self.override_bound = None
        self.max_num_stops = MAX_NUM_STOPS
        self.encoder = EncoderEnum.Direct
        self.structs = []
