# Building blocks for SL SMT theorysymbols
SL_PREFIX = "sl."
SEP_CON_SUFFIX = "sepcon"
SUBMODEL_SUFFIX = "submodel"
CONJUNCTION_SUFFIX = "conj"
DISJUNCTION_SUFFIX = "disj"
NEGATION_SUFFIX = "neg"
LOC_SUFFIX = ".loc"
NULL_SUFFIX = ".null"
SEG_SUFFIX = ".seg"
DATA_PRED_SUFFIX = ".dpred"
UNARY_DP_SUFFIX = "unary"
POINTS_TO_SUFFIX = ".pointsto"
EQ_SUFFIX = ".eq"
NEQ_SUFFIX = ".neq"

SEP_CON = SL_PREFIX + SEP_CON_SUFFIX # Untyped separating conjunction
SUBMODEL = SL_PREFIX + SUBMODEL_SUFFIX # Assert that this function's argument assertion holds in a submodel

# Fields
FLD_NEXT = "next"
FLD_PREV = "prev"
FLD_LEFT = "left"
FLD_RIGHT = "right"
FLD_PARENT = "parent"
FLD_DATA = "data"

# Predicates
TREE_PRED = "tree"
LIST_PRED = "list"
DLIST_PRED = "dlist"
PTREE_PRED = "ptree"

# Backends
QUANTIFIED_BACKEND = "quantified"
LAMBDA_BACKEND = "lambdas"

# Data
DATA_VAR_ZERO = "alpha"
DATA_VAR_ONE = "beta"

# Benchmark naming scheme
BM_EXPECT_BUG = "bug"
BM_EXPECT_ERROR = "error"
BM_EXPECT_UNSAT = "unsat"

MAX_PRED_VARS = 2

# Name construction functions
def seg_decl_name(struct, num_stops):
    num_suffix = str(num_stops) if num_stops > 1 else ""
    return struct.name + SEG_SUFFIX + num_suffix

def data_decl_name(struct, fld, num_stops):
    num_suffix = str(num_stops) if num_stops > 0 else ""
    if fld is not None:
        return struct.name + DATA_PRED_SUFFIX + "." + fld + num_suffix
    else:
        return struct.name + DATA_PRED_SUFFIX + "." + UNARY_DP_SUFFIX + num_suffix
