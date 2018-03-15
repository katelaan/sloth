import re

import z3

from .utils import logger
from .z3api import z3utils

###############################################################################
# Serialize Declarations
###############################################################################

def _smt_sort_str(sort):
    assert(isinstance(sort, z3.SortRef))
    #print("{} is array {}".format(sort.__class__, is_array(sort)))
    if z3utils.is_array_sort(sort):
        return "(Array {} {})".format(_smt_sort_str(sort.domain()), _smt_sort_str(sort.range()))
    else:
        return sort.name()

def _smt_const_decl(c):
    assert(isinstance(c, z3.ExprRef))
    assert(c.decl().arity() == 0)
    return "(declare-fun {} () {})".format(c, _smt_sort_str(c.decl().range()))

def _smt_list(ls):
    return "({})".format(" ".join(ls))

def _smt_fun_decl(f):
    assert(isinstance(f, z3.FuncDeclRef))
    dom = _smt_list([_smt_sort_str(f.domain(i)) for i in range(0,f.arity())])
    rng = _smt_sort_str(f.range())
    return "(declare-fun {} {} {})".format(f, dom, rng)

def _smt_sort_decl(sort):
    return "(declare-sort {} 0)".format(sort)

###############################################################################
# Serialize Expression
###############################################################################

def expr_to_smt2(encoding):
    # TODO: Is there really no API function for this? .sexpr() returns the internal representation with lots of annoying let statements and unreadable names. See also https://stackoverflow.com/a/11230129 - has anything changed since then?
    assert(isinstance(encoding, z3.ExprRef))

    def update(indent):
        return indent + 2

    pat = re.compile(r"\s+")

    def smtify(expr, children, indent):
        if z3.is_var(expr):
            # TODO: Allow more than one quantified var?
            assert(str(expr)=="Var(0)")
            return (" "*indent)+"_x_"
        elif z3.is_quantifier(expr):
            assert(expr.num_vars() == 1)

            return "{}({} ((_x_ {}))\n{})".format(
                " " * indent,
                "forall" if expr.is_forall else "exists",
                expr.var_sort(0),
                children[0]
            )
        else:
            assert(z3.is_app(expr))
            assert(isinstance(encoding, z3.ExprRef))
            child_string = "\n".join(children)
            stripped = pat.sub(" ", child_string)
            rep = stripped if len(stripped) < 20 else "\n"+child_string

            return "{}({}{})".format(
                " " * indent,
                translate_decl(expr),
                rep)

    def translate_decl(expr):
        assert(isinstance(expr.decl(),z3.FuncDeclRef))
        decl = expr.decl()
        s = str(decl)
        if s == "==": return "="
        elif z3.is_K(expr): #s == "K":
            # Const array => Must include type
            return "(as const {})".format(_smt_sort_str(decl.range()))
        elif z3.is_map(expr):
            # FIXME: Not general enough for data maps?
            return "(_ map {})".format(str(z3.get_map_func(expr)).lower())
        else: return s.lower()

    def leaf_to_smt(leaf, indent):
        s = str(leaf)
        if (s == "True" or s == "False"):
            s = s.lower()
        return (" "*indent) + s

    return z3utils.expr_fold_stateful(encoding, leaf_to_smt, smtify, update, 0)

###############################################################################
# Serialize Complete Encoding
###############################################################################

def write_encoding_to_file(file, encoding, structs):
    with open(file, "w") as f:
        f.write(serialize_encoding(encoding, structs))

def serialize_encoding(encoding, structs):
    assert(isinstance(encoding, z3.ExprRef))

    # Const decls
    consts = z3utils.collect_consts(encoding)
    ordered = sorted(consts, key=z3utils.by_complexity)
    const_decls = [_smt_const_decl(c) for c in ordered]

    # Generate sort-based decls based on the sorts for which we have constants
    sort_decls = []
    fun_refs = []

    # FIXME: With the lambda backend we declare functions for data structures that aren't used (because they all use the same sort, Int) => Determine based on parsed input instead?
    for struct in structs:
        sort = struct.sort
        if z3utils.contains_sort(consts, sort):
            if sort.to_declare():
                logger.debug("Declaring uninterpreted sort {}".format(sort))
                sort_decls.append(sort)
            fun_refs += struct.heap_fns()

    main_decls = ([_smt_sort_decl(s) for s in sort_decls]
                  + [_smt_fun_decl(f) for f in fun_refs])

    # Full list of declarations
    decls = main_decls + const_decls

    # use our encoding of the assertion directly for readability
    smt2_encoding = expr_to_smt2(encoding)
    assertion = "(assert \n  {}\n)".format(smt2_encoding)
    checks = "(check-sat)\n(get-model)"
    # TODO: Re-enable set-logic for the quantified backend?
    logic = "" # "(set-logic AUFLIA)" + "\n"
    full_encoding = logic + "\n".join(decls) + "\n" + assertion + "\n" + checks + "\n"
    return full_encoding
