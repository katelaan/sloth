from .. import config
from .z3utils import Solver, is_sat, model, run_z3

if config.Z3_LIB_PATH:
    z3.init(config.Z3_LIB_PATH)
