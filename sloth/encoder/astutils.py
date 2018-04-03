"""Implementation of various typing / preprocessing passes used in
the encoding.

.. testsetup::

  from sloth import *
  from sloth.encoder.astutils import *
  from sloth.utils import utils

"""

from ..utils import utils
from .utils import EncoderState
from .constset import ConstantSet

def fold(f_inner, f_leaf, ast):
    if ast.is_leaf():
        return f_leaf(ast)
    else:
        # List rather than genexpr to force evaluation
        child_results = [fold(f_inner, f_leaf, child) for child in ast]
        return f_inner(ast, child_results)

def consts_by_struct(ast, structs):
    """Return a map from `structs` to the set of constants per struct.

    >>> t = processed_ast(sts, sl.tree.pointsto("a", "b", "c"))
    >>> utils.print_unique_repr(consts_by_struct(t, sts))
    {Struct(sl.dlist): {}, Struct(sl.list): {}, Struct(sl.ptree): {}, Struct(sl.tree): {a, b, c}}

    """

    d_aux = {s : set() for s in structs}
    def f_inner(obj, _):
        # All variables are in the leaves
        pass
    def f_leaf(obj):
        nonlocal d_aux
        for c in obj.loc_consts():
            d_aux[obj.struct].add(c)
    fold(f_inner, f_leaf, ast)
    return d_aux

def pred_calls(ast):
    """Returns the set of all predicate calls that occur in this AST.

    >>> t = ast(sts, And(sl.sepcon(sl.list("l"), sl.tree.left("a","b")), sl.list.dpred.next(sl.alpha < sl.beta, "l")))
    >>> pred_calls(t)
    {...}
    >>> sorted(pred_calls(t), key=str)
    [PredCall('sl.list', 'next', DataAtom(sl.alpha < sl.beta), l), PredCall('sl.list', None, None, l)]

    """

    def f_leaf(obj):
        if obj.is_pred_call():
            return set([obj])
        else:
            return set()
    def f_inner(obj, child_results):
        return utils.merge_sets(*child_results)
    return fold(f_inner, f_leaf, ast)

def occurring_structs(ast):
    """Returns the set of all structures that occur in this AST.

    >>> get_structs = lambda expr : sorted(map(str,list(occurring_structs(ast(sts, expr)))))
    >>> a = Int("a")
    >>> get_structs(a < 23)
    []
    >>> get_structs(sl.list("l"))
    ['sl.list']
    >>> get_structs(And(sl.sepcon(sl.list("l"), sl.tree("t")), a < 23))
    ['sl.list', 'sl.tree']

    """
    def f_leaf(obj):
        try:
            return {obj.struct}
        except AttributeError:
            # No struct info => Must be a data formula
            assert(obj.is_data())
            return set()
    def f_inner(obj, child_results):
        return utils.merge_sets(*child_results)
    return fold(f_inner, f_leaf, ast)
