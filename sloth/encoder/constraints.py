import operator
import textwrap

import z3

from ..backend import symbols
from ..utils import utils

class ConstraintList:
    def __init__(self):
        self.constraints = []

    def append_constraint(self, constraint):
        assert(isinstance(constraint, SmtConstraint))
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

class SmtConstraint:

    def __str__(self):
        return pretty_print(self)

    def is_leaf(self):
        return False

    def __iter__(self):
        raise NotImplementedError('')

    def to_z3_expr(self):
        raise NotImplementedError('')

def pretty_print(constraint, indent = '  '):
    # TODO: Return valid SMT2 expression? (by rewriting operators to lower case etc.)
    assert(isinstance(constraint, SmtConstraint))

    lines = []

    if constraint.sl_expr is not None:
        lines.append(';; {}'.format(constraint.sl_expr))
    if constraint.description is not None:
        lines.append(';; ' + constraint.description)

    if constraint.is_leaf():
        lines.append('(' + str(constraint.to_z3_expr()) + ')')
    else:
        #lines.append('(' + type(constraint).__name__.lower())
        lines.append('(' + type(constraint).__name__)
        try:
            it = iter(constraint)
        except (AttributeError, NotImplementedError):
            msg = 'No iteration for {}'.format(type(constraint).__name__)
            raise utils.SlothException(msg) from None
        else:
            for child in constraint:
                child_str = pretty_print(child, indent)
                lines.append(textwrap.indent(child_str, indent))
        lines.append(')')

    return '\n'.join(lines)

class BaseConstraint(SmtConstraint):
    def __init__(self, constraint, sl_expr = None, description = None):
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
        self.constraint = constraint
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
