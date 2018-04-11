import re, textwrap

import z3

from .utils import logger
from .z3api import z3utils

###############################################################################
# Serialize Declarations
###############################################################################

def smt_sort_str(sort):
    assert isinstance(sort, z3.SortRef), \
        "Received {} of type {} != SortRef".format(c, type(c).__name__)
    if z3utils.is_array_sort(sort):
        return '(Array {} {})'.format(smt_sort_str(sort.domain()), smt_sort_str(sort.range()))
    else:
        return sort.name()

def smt_const_decl(c):
    assert isinstance(c, z3.ExprRef), \
        "Received {} of type {} != ExprRef".format(c, type(c).__name__)
    assert c.decl().arity() == 0, \
        "Received {} of arity {} != 0 as const decl".format(c, c.decl().arity())
    return '(declare-fun {} () {})'.format(c, smt_sort_str(c.decl().range()))

def smt_list(ls):
    return '({})'.format(' '.join(ls))

def smt_fun_decl(f):
    assert isinstance(f, z3.FuncDeclRef), \
        "Received {} of type {} != FuncDeclRef".format(f, type(f).__name__)
    dom = smt_list([smt_sort_str(f.domain(i)) for i in range(0,f.arity())])
    rng = smt_sort_str(f.range())
    return '(declare-fun {} {} {})'.format(f, dom, rng)

def smt_sort_decl(sort):
    return '(declare-sort {} 0)'.format(sort)

###############################################################################
# Serialize Expression
###############################################################################

def translate_head_func_decl(expr):
    decl = expr.decl()
    assert isinstance(decl,z3.FuncDeclRef)
    s = str(decl)
    if s == '==': return '='
    elif z3.is_K(expr): #s == 'K':
        # Const array => Must include type
        return '(as const {})'.format(smt_sort_str(decl.range()))
    elif z3.is_map(expr):
        # FIXME: Not general enough for data maps?
        return '(_ map {})'.format(str(z3.get_map_func(expr)).lower())
    else: return s.lower()

def expr_to_smt2_string(encoding, multi_line = True, indent = '  '):
    assert(isinstance(encoding, z3.ExprRef))

    if not multi_line:
        indent = ''

    pat = re.compile(r'\s+')

    def smtify(expr, children):
        if z3.is_var(expr):
            # TODO: Allow more than one quantified var?
            assert str(expr)=='Var(0)', \
                'Currently only support for expressions with a single quantified variable'
            return '_x_'
        elif z3.is_quantifier(expr):
            assert expr.num_vars() == 1, \
                'Currently only support for expressions with a single quantified variable'

            return '{}({} ((_x_ {}))\n{})'.format(
                'forall' if expr.is_forall() else 'exists',
                expr.var_sort(0),
                children[0]
            )
        else:
            #print('{!r} with children {!r}'.format(expr, children))
            assert z3.is_app(expr)
            assert isinstance(encoding, z3.ExprRef)
            # TODO: Improve/simplify the whitespace handling
            sjoin = '\n' if multi_line else ' '
            child_string = sjoin.join(children)
            if indent:
                child_string = textwrap.indent(child_string, indent)
            stripped = pat.sub(' ', child_string)
            while stripped[0] == ' ':
                stripped = stripped[1:]
            if len(stripped) < 20 or not multi_line:
                rep = stripped
            else:
                rep = '\n' + child_string

            res = '({} {})'.format(
                translate_head_func_decl(expr),
                rep)
            #print('Will return {}'.format(res))
            return res

    def leaf_to_smt(leaf):
        #print('Leaf: {!r}'.format(leaf))
        s = str(leaf)
        if (s == 'True' or s == 'False'):
            return s.lower()
        else:
            return s

    return z3utils.expr_fold(encoding, leaf_to_smt, smtify)

###############################################################################
# Serialize Complete Encoding
###############################################################################

def write_encoding_to_file(file, encoding, structs):
    with open(file, 'w') as f:
        f.write(serialize_encoding(encoding, structs))

def serialize_encoding(encoding, structs):
    assert(isinstance(encoding, z3.ExprRef))

    # Const decls
    consts = z3utils.collect_consts(encoding)
    ordered = sorted(consts, key=z3utils.by_complexity)
    const_decls = [smt_const_decl(c) for c in ordered]

    # Generate sort-based decls based on the sorts for which we have constants
    sort_decls = []
    fun_refs = []

    # FIXME: With the lambda backend we declare functions for data structures that aren't used (because they all use the same sort, Int) => Determine based on parsed input instead?
    for struct in structs:
        sort = struct.sort
        if z3utils.contains_sort(consts, sort):
            if sort.to_declare():
                logger.debug('Declaring uninterpreted sort {}'.format(sort))
                sort_decls.append(sort)
            fun_refs += struct.heap_fns()

    main_decls = ([smt_sort_decl(s) for s in sort_decls]
                  + [smt_fun_decl(f) for f in fun_refs])

    # Full list of declarations
    decls = main_decls + const_decls

    # use our encoding of the assertion directly for readability
    smt2_encoding = expr_to_smt2_string(encoding)
    assertion = '(assert \n  {}\n)'.format(smt2_encoding)
    checks = '(check-sat)\n(get-model)'
    # TODO: Re-enable set-logic for the quantified backend?
    logic = '' # '(set-logic AUFLIA)' + '\n'
    full_encoding = logic + '\n'.join(decls) + '\n' + assertion + '\n' + checks + '\n'
    return full_encoding
