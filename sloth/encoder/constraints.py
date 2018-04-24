import itertools
import operator
import textwrap

import z3

from .. import serialization
from ..backend import symbols, generic
from ..model import model
from ..utils import utils
from . import astutils
from . import constset as cs

class ConstraintList:
    def __init__(self):
        self.constraints = []

    def append_constraint(self, constraint):
        assert isinstance(constraint, SmtConstraint), "Can't use {} as SmtConstraint".format(type(constraint).__name__)
        self.constraints.append(constraint)

    def append_expr(self, constraint, sl_expr = None, description = None):
        if not isinstance(constraint, z3.ExprRef):
            msg = "Can't use {} of type {} as SMT constraint"
            raise utils.SlothException(msg.format(constraint, type(constraint).__name__))
        else:
            self.constraints.append(BaseConstraint(constraint, sl_expr, description))

    def to_conjunction(self, sl_expr = None, description = None):
        return And(*self.constraints, sl_expr = sl_expr, description = description)

    def to_disjunction(self, sl_expr = None, description = None):
        return Or(*self.constraints, sl_expr = sl_expr, description = description)

    @classmethod
    def from_list(cls, exprs):
        cs = cls()
        for expr in exprs:
            cs.append_constraint(as_constraint(expr))
        return cs

def as_constraint(expr, sl_expr = None, description = None):
    if isinstance(expr, SmtConstraint):
        return expr
    else:
        assert isinstance(expr, z3.ExprRef), 'Unexpected type {}'.format(type(expr).__name__)
        return BaseConstraint(expr, sl_expr = sl_expr, description = description)

def from_list(ls):
    return ConstraintList.from_list(ls)

class SmtConstraint:

    def __init__(self, sl_expr, description):
        assert sl_expr is None or isinstance(sl_expr, z3.ExprRef)
        assert description is None or isinstance(description, str)
        self.sl_expr = sl_expr
        self.description = description

    def __str__(self):
        return pretty_print(self)

    def is_leaf(self):
        return False

    def __iter__(self):
        raise NotImplementedError('')

    def to_z3_expr(self):
        raise NotImplementedError('')

def to_commented_z3_string(constraint):
    "Convert `constraint` into the SMTLIB variant supported by z3"
    def pretty_print_op(constraint):
        res = type(constraint).__name__.lower()
        d = {
            'implies': '=>',
            'iff': '='
        }
        return d.get(res, res)

    return pretty_print(constraint,
                        pretty_print_expr = serialization.expr_to_smt2_string,
                        pretty_print_op = pretty_print_op)

def pretty_print(constraint, indent = '  ',
                 pretty_print_expr = lambda e: '({})'.format(e),
                 pretty_print_op = lambda c : type(c).__name__):
    """Pretty-print the constraint.

    By default, uses representation close to the z3 python notation
    rather than returning a valid smt2lib string.

    See :func:`to_commented_z3_string` for a wrapper that changes the
    behavior to genrate SMTLIB strings instead.

    """
    assert isinstance(constraint, SmtConstraint), "Can't treat {} as SmtConstraint".format(type(constraint).__name__)

    lines = []

    if constraint.sl_expr is not None:
        lines.append(';; {}'.format(serialization.expr_to_smt2_string(constraint.sl_expr, multi_line = False)))
    if constraint.description is not None:
        lines.append(';; ' + constraint.description)

    if constraint.is_leaf():
        lines.append(pretty_print_expr(constraint.to_z3_expr()))
    else:
        lines.append('(' + pretty_print_op(constraint))
        try:
            it = iter(constraint)
        except (AttributeError, NotImplementedError):
            msg = 'No iteration for {}'.format(type(constraint).__name__)
            raise utils.SlothException(msg) from None
        else:
            for child in constraint:
                child_str = pretty_print(child, indent, pretty_print_expr, pretty_print_op)
                lines.append(textwrap.indent(child_str, indent))
        lines.append(')')

    return '\n'.join(lines)

class BaseConstraint(SmtConstraint):
    def __init__(self, constraint, sl_expr = None, description = None):
        assert isinstance(constraint, z3.ExprRef)
        self.constraint = constraint
        super().__init__(sl_expr, description)

    def __iter__(self):
        return iter()

    def __repr__(self):
        cls_name = type(self).__name__
        return '{}({!r}, {!r}, {!r})'.format(cls_name, self.constraint, self.sl_expr, self.description)

    def is_leaf(self):
        return True

    def to_z3_expr(self):
        return self.constraint

class VarArgOp(SmtConstraint):
    def __init__(self, *constraints, sl_expr = None, description = None):
        if not constraints:
            constraints = [type(self).neutral]
        self.constraints = [as_constraint(c) for c in constraints]
        super().__init__(sl_expr, description)

    def __repr__(self):
        cls_name = type(self).__name__
        constraints = ', '.join(map(repr, self.constraints))
        return '{}({}, {!r}, {!r})'.format(cls_name, constraints, self.sl_expr, self.description)

    def __iter__(self):
        return iter(self.constraints)

class And(VarArgOp):

    neutral = symbols.Z3True

    def to_z3_expr(self):
        return symbols.LAnd([c.to_z3_expr() for c in self.constraints])

class Or(VarArgOp):

    neutral = symbols.Z3False

    def to_z3_expr(self):
        return symbols.LOr([c.to_z3_expr() for c in self.constraints])

class Not(SmtConstraint):
    def __init__(self, constraint, sl_expr = None, description = None):
        self.constraint = as_constraint(constraint)
        super().__init__(sl_expr, description)

    def __iter__(self):
        yield self.constraint

    def to_z3_expr(self):
        return z3.Not(self.constraint.to_z3_expr())

class BinOp(SmtConstraint):

    op = None

    def __init__(self, left, right, sl_expr = None, description = None):
        self.left = as_constraint(left)
        self.right = as_constraint(right)
        super().__init__(sl_expr, description)

    def __iter__(self):
        yield self.left
        yield self.right

    def __repr__(self):
        cls_name = type(self).__name__
        return '{}(left = {!r}, right = {!r}, sl_expr = {!r}, description = {!r})'.format(cls_name, self.left, self.right, self.sl_expr, self.description)

    def to_z3_expr(self):
        return type(self).op(self.left.to_z3_expr(), self.right.to_z3_expr())

class Implies(BinOp):
    op = z3.Implies

class Iff(BinOp):
    op = operator.eq


class SmtDecls:
    def __init__(self, consts = [], funs = [], sorts = []):
        self.consts = list(consts)
        self.funs = list(funs)
        self.sorts = list(sorts)

    def _to_ref(self, c):
        if isinstance(c, z3.ExprRef):
            return c
        else:
            assert isinstance(c, generic.Set), \
                "Can't convert {} of type {} to z3 expression reference".format(c, type(c).__name__)
            return c.ref

    def to_smt2_string(self):
        sorts = sorted(map(serialization.smt_sort_decl, self.sorts))
        # TODO: Convert FPs to refs
        consts = sorted(map(serialization.smt_const_decl, map(self._to_ref, self.consts)))
        funs = sorted(map(serialization.smt_fun_decl, self.funs))
        all_decls = itertools.chain(sorts, consts, funs)
        return '\n'.join(all_decls)

    @classmethod
    def from_iterable(cls, decls):
        consts = []
        funs = []
        for d in decls:
            #print('{} {}'.format(d, type(d).__name__))
            if isinstance(d, z3.FuncDeclRef):
                funs.append(d)
            else:
                assert isinstance(d, z3.ExprRef) or isinstance(d, generic.Set), \
                    "Can't treat {} of type {} as declaration".format(d, type(d).__name__)
                consts.append(d)
        return cls(consts, funs)


class Z3Input:
    def __init__(self, constraint, encoded_ast = None, decls = None):
        self.constraint = constraint
        self.encoded_ast = encoded_ast
        if isinstance(decls, SmtDecls):
            self.decls = decls
        else:
            self.decls = SmtDecls.from_iterable(decls)
        self.structs = astutils.structs_in_ast(self.encoded_ast)

    def to_smt2_string(self, check_sat = True, get_model = True, minify = False):
        cmds = ''
        if check_sat:
            cmds += '\n(check-sat)'
        if get_model:
            cmds += '\n(get-model)'

        if minify:
            body = serialization.expr_to_smt2_string(self.constraint.to_z3_expr(), multi_line = False)
        else:
            body = textwrap.indent(to_commented_z3_string(self.constraint), '  ')

        return '{}\n(assert\n{}\n){}\n'.format(
            self.decls.to_smt2_string(),
            body,
            cmds
        )

    def to_z3_expr(self):
        return self.constraint.to_z3_expr()

    def to_file(self, filename, check_sat = True, get_model = True, minify = False):
        with open(filename, 'w') as f:
            f.write(self.to_smt2_string(check_sat, get_model, minify))

    def all_consts(self):
        """Return the set of all constants present in the encoded SL expr or introduced in the encodeing"""
        if self.encoded_ast is None:
            raise utils.SlothException("No SL AST defined => Can't compute constants")
        else:
            consts = cs.ConstantSet(self.structs)
            consts_by_struct = astutils.consts_by_struct(self.encoded_ast)
            for struct, locs in consts_by_struct.items():
                consts.add_loc_consts(struct, *locs)
            consts.add_data_consts(*astutils.data_consts(self.encoded_ast))
            #print ('Decls: {}'.format(self.decls))
            for decl in self.decls.consts:
                # TODO: Properly add consts. Problem: Introduced loc/FP consts are not stored by struct. It's unclear whether we want to have per-struct FPs in the long run anyway, so we can decide what to do about this later
                # FIXME: Non-FP consts introduced by the encoding are not added at all. Is that what we want. (it might actually be, because we don't really care about the auxiliary variables from the unfolding)
                if isinstance(decl, generic.Set):
                    sdecl = str(decl)
                    #print('Processing FP var {}'.format(sdecl))
                    for s in self.structs:
                        for f in s.fields:
                            if sdecl.find(f) != -1:
                                # Note that this way we add data fp vars to all structs
                                #print('Adding {} to the struct model for {} because of match for field {}'.format(sdecl, s, f))
                                consts.add_fp_consts(s, decl)
                                break

            return consts

    def label_model(self, z3model):
        consts = self.all_consts()
        return model.SmtModel(z3model, consts, consts.structs)
