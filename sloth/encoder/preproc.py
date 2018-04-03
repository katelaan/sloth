"""SL AST preprocessing.

.. testsetup::

  from sloth import *
  from sloth.encoder.preproc import *
  from z3 import *

>>> expr = sl.sepcon(sl.list("a"), sl.list.seg("b", "c"))
>>> spatial = ast(sts, expr)
>>> assign_negation_to_leaves(spatial)
>>> not(spatial[0].is_under_negation or spatial[1].is_under_negation)
True
>>> spatial = ast(sts, Not(expr))
>>> assign_negation_to_leaves(spatial)
>>> spatial[0][0].is_under_negation and spatial[0][1].is_under_negation
True


"""

from . import slast, astutils
from .utils import EncoderState
from ..utils import utils

def assign_ids(ast):
    """Assign unique ID to each node.

    Use case: Ensure unique but short footprint names to avoid
    wrong models for formulas like list(x) * list(x) * x !=
    null.

    >>> t = ast(sts, sl.sepcon(sl.list("x"), sl.list("x")))
    >>> SlAst.id_ = [0]
    >>> assign_ids(t)
    >>> t[0], t[0].id_
    (PredCall('sl.list', None, None, x), 0)
    >>> t[1], t[1].id_
    (PredCall('sl.list', None, None, x), 1)

    """
    def f_either(obj, *child_results):
        id_ = slast.SlAst.id_
        obj.id_ = id_[0]
        id_[0] += 1

    # def f_either(obj, *child_results):
    #     _id_dict = slast.SlAst._id_dict
    #     id_ = slast.SlAst.id_
    #     # FIXME: Assign same id to all data predicate calls with the same root/stop-nodes
    #     key = str(obj.to_sl_expr())
    #     if key in _id_dict:
    #         obj.id_ = _id_dict[key]
    #     else:
    #         obj.id_ = id_[0]
    #         _id_dict[key] = id_[0]
    #         id_[0] += 1

    astutils.fold(f_either, f_either, ast)

def assign_negation_to_leaves(obj, parent_under_negation = False):
    if not isinstance(obj, slast.SlAst):
        msg = "Can't assign negation to non-AST object {}"
        raise utils.SlothException(msg.format(type(obj).__name__))
    obj.is_under_negation = parent_under_negation
    for child in obj:
        if isinstance(obj, slast.SlNot):
            child_neg = not parent_under_negation
        else:
            child_neg = parent_under_negation
        assign_negation_to_leaves(child, child_neg)
    obj.state = EncoderState.PreprocFinished
