import itertools

import z3

from . import consts
from .backend import symbols
from .utils import logger, utils

class ParseException(utils.SlothException):
    """Raised when an error occurs during pparsing"""

def sort_decls(structs):
    """Generate the set of all (uninterpreted) sort declarations from a set of predefined structures.

    Return (possibly empty) dictionary of sort declarations suitable for z3 python API."""
    sorts = [struct.sort.ref for struct in structs
             if struct.sort.to_declare()]
    return { str(s) : s for s in sorts }

def fun_decls(structs, other_decls):
    """Generate the set of all SMT function declarations from a set of predefined structures as well as other hardcoded declarations."""
    return utils.merge_dicts(
        # TODO: Can we set the :left-assoc and/or :right-assoc attribute to allow more than two args?
        other_decls,
        *[struct.decl_map() for struct in structs]
    )

def rewrite_for_backend(sl_str, structs):
    backend_str = sl_str
    for struct in structs:
        if struct.input_sort_name != str(struct.sort):
            logger.debug("Performing replacement for {}".format(struct))
            backend_str = backend_str.replace(struct.input_sort_name, str(struct.sort))

    if sl_str != backend_str:
        logger.info("Input for current backend:\n{}".format(backend_str))

    return backend_str

def parse_sl(sl_str, structs, other_decls = symbols.decls):
    """Parse the given SL SMT2 input string into Z3 expression,
    assuming predefined structures as defined by structs,
    as well as other function declarations (defaulting to the global SL declarations).

    Return (possibly empty) dictionary of func declarations suitable for z3 python API."""
    assert(isinstance(sl_str, str))

    logger.info("Unprocessed input:\n{}".format(sl_str))

    backend_str = rewrite_for_backend(sl_str, structs)

    sorts = sort_decls(structs)
    decls = fun_decls(structs, other_decls)

    if logger.debug_logging_enabled():
        logger.debug("SL SUMMARY")
        symbols.print_sl_summary(structs)
        logger.debug("As assigned to maps:")
        logger.debug("Sorts: {}".format(sorts))
        logger.debug("Uninterpreted functions: {}".format(decls))

    if sl_str.startswith(';; bound = '):
        max_depth = int(''.join(list(itertools.takewhile(lambda c : c.isdigit(), sl_str[11:]))))
    else:
        max_depth = None

    try:
        return (z3.parse_smt2_string(backend_str, sorts = sorts, decls = decls), max_depth)
    except z3.Z3Exception as e:
        raise ParseException("{}".format(e))

def parse_sl_file(input_file, structs, other_decls = symbols.decls):
    """Parse the given input file (relative path, not checked for existence),
    assuming predefined structures as defined by structs,
    as well as other function declarations (defaulting to the global SL declarations)

    Return Z3 expression reference."""
    with open(input_file, "r") as f:
        content = f.read()
        parsed = parse_sl(content, structs, other_decls)
        return(parsed[0])
