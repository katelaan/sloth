"""Implementation of various typing / preprocessing passes used in
the encoding.

.. testsetup::

   import z3
   from sloth import *
   from sloth.encoder.astbuilder import ast
   from sloth.utils import utils

"""

import collections

from ..utils import utils
from . import slast

def fold(f_inner, f_leaf, ast):
    if ast.is_leaf():
        return f_leaf(ast)
    else:
        # List rather than genexpr to force evaluation
        child_results = [fold(f_inner, f_leaf, child) for child in ast]
        return f_inner(ast, child_results)

def atoms(ast):
    """Generate all atomic formulas in the AST. (With duplicates, if any.)

    >>> list(atoms(ast(sl.structs, z3.And(sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z')), z3.Not(sl.list.pointsto('z', 'y'))))))
    [PointsTo('sl.list', x, y), SpatialEq(x, z, False), PointsTo('sl.list', z, y)]

    """
    if ast.is_leaf():
        yield ast
    else:
        for child in ast:
            yield from atoms(child)

AtomWithPolarity = collections.namedtuple('AtomWithPolarity', 'atom is_negated')

def atoms_with_polarity(ast, root_is_negated = False):
    """Generate all atomic formulas in the AST together with a flag whether they are under negation.

    (Returns duplicates, if any.)

    >>> list(atoms_with_polarity(ast(sl.structs, z3.And(sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z')), z3.Not(sl.list.pointsto('z', 'y'))))))
    [AtomWithPolarity(atom=PointsTo('sl.list', x, y), is_negated=False), AtomWithPolarity(atom=SpatialEq(x, z, False), is_negated=False), AtomWithPolarity(atom=PointsTo('sl.list', z, y), is_negated=True)]
    >>> list(atoms_with_polarity(ast(sl.structs, z3.And(z3.Not(z3.Not(sl.sepcon(sl.list.pointsto('x', 'y'), sl.list.eq('x', 'z')))), z3.Not(sl.list.pointsto('z', 'y'))))))
    [AtomWithPolarity(atom=PointsTo('sl.list', x, y), is_negated=False), AtomWithPolarity(atom=SpatialEq(x, z, False), is_negated=False), AtomWithPolarity(atom=PointsTo('sl.list', z, y), is_negated=True)]

    """
    if ast.is_leaf():
        yield AtomWithPolarity(ast, root_is_negated)
    else:
        is_not = isinstance(ast, slast.SlNot)
        for child in ast:
            yield from atoms_with_polarity(child, root_is_negated != is_not)

def contains_calls(ast):
    for atom in atoms(ast):
        if atom.is_pred_call():
            return True
    return False

def consts_by_struct(ast):
    """Return a map from each struct in the AST to the set of constants of that struct.

    >>> t = ast(sl.structs, sl.sepcon(sl.list.seg('x', 'y'), sl.tree.pointsto('a', 'b', 'c')))
    >>> utils.print_unique_repr(consts_by_struct(t))
    {Struct(sl.list): {x, y}, Struct(sl.tree): {a, b, c}}

    """

    d_aux = {}
    def f_inner(obj, _):
        # All variables are in the leaves
        pass
    def f_leaf(obj):
        nonlocal d_aux
        for c in obj.loc_consts():
            d_aux.setdefault(obj.struct, set()).add(c)
    fold(f_inner, f_leaf, ast)
    return d_aux

def data_preds_by_struct(ast):
    """Return a map from each struct in the AST to the data preds that occur in the AST.

    >>> t = ast(sl.structs, sl.sepcon(sl.list.dpred.next(sl.alpha < sl.beta, 'x'), sl.tree.dpred.left(sl.alpha < sl.beta, 't'), sl.tree.dpred.unary(sl.alpha < 32, 'u')))
    >>> utils.print_unique_repr(data_preds_by_struct(t))
    {Struct(sl.list): [('next', DataAtom(sl.alpha < sl.beta))], Struct(sl.tree): [('left', DataAtom(sl.alpha < sl.beta)), (None, DataAtom(sl.alpha < 32))]}

    """
    d_aux = {}
    def f_inner(obj, _):
        # All calls are in the leaves
        pass
    def f_leaf(obj):
        nonlocal d_aux
        if obj.is_pred_call():
            if obj.pred is not None:
                d_aux.setdefault(obj.struct, []).append((obj.fld,obj.pred))
    fold(f_inner, f_leaf, ast)
    return d_aux

def data_consts(ast):

    s_aux = set()
    def f_inner(obj, _):
        # All variables are in the leaves
        pass
    def f_leaf(obj):
        nonlocal s_aux
        for c in obj.data_consts():
            s_aux.add(c)
    fold(f_inner, f_leaf, ast)
    return s_aux

def pred_calls(ast):
    """Returns the set of all predicate calls that occur in this AST.

    >>> t = ast(sl.structs, And(sl.sepcon(sl.list("l"), sl.tree.left("a","b")), sl.list.dpred.next(sl.alpha < sl.beta, "l")))
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

def structs_in_ast(ast):
    """Returns the set of all structures that occur in this AST.

    >>> get_structs = lambda expr : sorted(map(str,list(structs_in_ast(ast(sl.structs, expr)))))
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
