import operator
import textwrap

import z3

from .. import serialization
from ..backend import symbols
from ..utils import utils

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
        lines.append(';; {}'.format(constraint.sl_expr))
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
        self.sl_expr = sl_expr
        self.description = description

    def __iter__(self):
        return iter()

    def is_leaf(self):
        return True

    def to_z3_expr(self):
        return self.constraint

class VarArgOp(SmtConstraint):
    def __init__(self, *constraints, sl_expr = None, description = None):
        self.constraints = [as_constraint(c) for c in constraints]
        self.sl_expr = sl_expr
        self.description = description

    def __iter__(self):
        return iter(self.constraints)

class And(VarArgOp):

    def to_z3_expr(self):
        return symbols.LAnd([c.to_z3_expr() for c in self.constraints])

class Or(VarArgOp):
    def to_z3_expr(self):
        return symbols.LOr([c.to_z3_expr() for c in self.constraints])

class Not(SmtConstraint):
    def __init__(self, constraint, sl_expr = None, description = None):
        self.constraint = as_constraint(constraint)
        self.sl_expr = sl_expr
        self.description = description

    def __iter__(self):
        yield self.constraint

    def to_z3_expr(self):
        return z3.Not(self.constraint)

class BinOp(SmtConstraint):

    op = None

    def __init__(self, left, right, sl_expr = None, description = None):
        self.left = as_constraint(left)
        self.right = as_constraint(right)
        self.sl_expr = sl_expr
        self.description = description

    def __iter__(self):
        yield self.left
        yield self.right

    def to_z3_expr(self):
        return self.op(self.constraint)

class Implies(BinOp):
    op = z3.Implies

class Iff(BinOp):
    op = operator.eq


class Z3Input:
    def __init__(self, constraint, decls = None):
        self.constraint = constraint
        self.decls = decls
