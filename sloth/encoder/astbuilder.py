"""Building ASTs

.. testsetup::

  from sloth import *
  from sloth.encoder.astbuilder import *
  from z3 import *

From :class:`z3.ExprRef` to :class`SlAstManager` and back:

>>> expr = sl.sepcon(sl.list("a"), sl.list.seg("b", "c"))
>>> ast(sts, expr)
SepCon(PredCall('sl.list', None, None, a), PredCall('sl.list', None, None, b, c))
>>> ast(sts, expr).to_sl_expr()
sl.sepcon(sl.list(a), sl.list.seg(b, c))
>>> expr = And(sl.sepcon(sl.list("a"), sl.list.seg("b", "c")), sl.list.dpred.next(sl.alpha < sl.beta, "a"))
>>> ast(sts, expr)
SlAnd(SepCon(PredCall('sl.list', None, None, a), PredCall('sl.list', None, None, b, c)), PredCall('sl.list', 'next', DataAtom(sl.alpha < sl.beta), a))
>>> ast(sts, expr).to_sl_expr()
And(sl.sepcon(sl.list(a), sl.list.seg(b, c)),
    sl.list.dpred.next(sl.alpha < sl.beta, a))

Checking properties of the SL assertions:

>>> expr = sl.sepcon(sl.list("a"), sl.list.seg("b", "c"))
>>> spatial = ast(sts, expr)
>>> spatial.is_positive()
True
>>> ast(sts, Not(expr)).is_positive()
False

For documentation of the actual encoding, see the individual
:class:`SlAst` classes.

"""

import functools
from collections import Sequence

import z3

from .. import config
from ..backend import symbols
from ..z3api import rewriter
from . import typing, preproc
from .slast import *

def apply_to_children(fun):
    def ignore_root(root, children):
        try:
            return fun(*children)
        except TypeError as e:
            msg = "Can't construct AST for {} / {}. Wrong arity?"
            raise TypeError(msg.format(root, children))
    return ignore_root

def apply_to_args_and_children(fun, *args):
    return apply_to_children(functools.partial(fun, *args))

def rewrite_with_dictionary(expr, rewriting_dict):
    def default_fn(n, new_args):
        if is_const(n):
            return n
        else:
            return DataAtom(n)
    return rewriter.tree_conditional_rewrite(expr, rewriting_dict, default_fn)

def pure_rewriting_dict():
    return {
        symbols.and_decl : apply_to_children(SlAnd),
        symbols.or_decl : apply_to_children(SlOr),
        symbols.not_decl : apply_to_children(SlNot)
    }

def construct_pure_tree(expr):
    """Converts the given :class:`z3.ExprRef` of a pure formula into an
:class:`SlAst`.

    >>> a, b = Ints("a b")
    >>> construct_pure_tree(a == b)
    DataAtom(a == b)
    >>> expr = And(a == b, Or(a < b, Not(a > b)))
    >>> t = construct_pure_tree(expr)
    >>> t
    SlAnd(DataAtom(a == b), SlOr(DataAtom(a < b), SlNot(DataAtom(a > b))))
    >>> eq(t.to_sl_expr(), expr)
    True

    """
    return rewrite_with_dictionary(expr, pure_rewriting_dict())

def spatial_rewriting_dict(structs):
    rewriting_dict = {
        symbols.and_decl : apply_to_children(SlAnd),
        symbols.or_decl : apply_to_children(SlOr),
        symbols.not_decl : apply_to_children(SlNot),
        symbols.sep_con_fn : apply_to_children(SepCon)
    }
    for struct in structs:
        # Points-to assertions
        rewriting_dict.update([(struct.points_to_predicate(),
                                apply_to_args_and_children(PointsTo, struct))])
        fld_funs = [(struct.fld_predicate(fld),
                    apply_to_children(functools.partial(PointsToSingleField, struct, fld)))
                    for fld in struct.fields]
        rewriting_dict.update(fld_funs)
        # (Dis-)equality assertions
        rewriting_dict.update([(struct.equality_predicate(),
                                apply_to_args_and_children(SpatialEq, struct, False))])
        rewriting_dict.update([(struct.disequality_predicate(),
                                apply_to_args_and_children(SpatialEq, struct, True))])
        # Non-data predicate calls
        constructor = apply_to_args_and_children(PredCall, struct, None, None)
        rewriting_dict.update([(struct.predicate(), constructor)])
        num_stops = config.max_num_stops(struct)
        seg_preds = (
            (struct.segment_predicate(i+1), constructor)
             for i in range(num_stops)
        )
        rewriting_dict.update(seg_preds)
        # Data predicate calls
        for f in struct.fields:
            constructor = apply_to_args_and_children(PredCall, struct, f)
            num_stops = config.max_num_stops(struct)
            data_preds = (
                (struct.data_predicate(f, i), constructor)
                for i in range(num_stops + 1)
            )
            rewriting_dict.update(data_preds)
        constructor = apply_to_args_and_children(PredCall, struct, None)
        unary_data_preds = (
                (struct.unary_data_predicate(i), constructor)
                for i in range(num_stops + 1)
            )
        rewriting_dict.update(unary_data_preds)
    return rewriting_dict

def construct_spatial_tree(expr, structs):
    """Converts the given :class:`z3.ExprRef` of a pure formula into an
:class:`SlAst`.

    >>> construct_spatial_tree(sl.list.pointsto("a", "b"), sts)
    PointsTo('sl.list', a, b)
    >>> construct_spatial_tree(sl.tree.left("a", "b"), sts)
    PointsToSingleField('sl.tree', 'left', a, b)
    >>> expr = sl.sepcon(sl.list("a"), sl.list.seg("b", "c"))
    >>> construct_spatial_tree(expr, sts)
    SepCon(PredCall('sl.list', None, None, a), PredCall('sl.list', None, None, b, c))
    >>> construct_spatial_tree(expr, sts).to_sl_expr()
    sl.sepcon(sl.list(a), sl.list.seg(b, c))
    >>> construct_spatial_tree(sl.tree.seg2("a", "b", "c"), sts).to_sl_expr()
    sl.tree.seg2(a, b, c)
    >>> dp = sl.list.dpred.next(sl.alpha < sl.beta, "x")
    >>> construct_spatial_tree(dp, sts)
    PredCall('sl.list', 'next', DataAtom(sl.alpha < sl.beta), x)
    >>> dp = sl.tree.dpred.right1(sl.alpha > sl.beta, "x", "y")
    >>> construct_spatial_tree(dp, sts)
    PredCall('sl.tree', 'right', DataAtom(sl.alpha > sl.beta), x, y)
    >>> construct_spatial_tree(dp, sts).to_sl_expr()
    sl.tree.dpred.right1(sl.alpha > sl.beta, x, y)

    """
    return rewrite_with_dictionary(expr, spatial_rewriting_dict(structs))

def full_rewriting_dict(structs):
    rewriting_dict = dict(spatial_rewriting_dict(structs))
    # TODO: It seems like the spatial dict now actually subsumes the pure dict. If that remains so, throw this out.
    rewriting_dict.update(pure_rewriting_dict())
    return rewriting_dict

def ast(structs, expr):
    assert(isinstance(structs, Sequence))
    assert(isinstance(expr, z3.ExprRef))
    # Ensure there's no And/Or with more than two args
    # -- otherwise our rewriter will fail!
    expr = typing.make_vararg_ops_binary(expr)
    return rewrite_with_dictionary(expr, full_rewriting_dict(structs))

def processed_ast(structs, expr):
    t = ast(structs, expr)
    preproc.assign_negation_to_leaves(t)
    preproc.assign_ids(t)
    return t
