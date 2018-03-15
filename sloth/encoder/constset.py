"""

.. testsetup::

  from sloth import *

"""

from ..model import model_utils # TODO: Remove cyclic dependency between packages
from ..backend import struct as struct_mod

class ConstantSet(object):
    """Represents a set of constants sorted by struct and kind
(loc/fp/data).

    >>> c = ConstantSet(sts)
    >>> c.add_data_consts(*Ints("a b"))
    >>> c
    consts(data={a,b})
    >>> c.add_loc_consts(sl.list.struct, *sl.list.locs("x", "y", "z"))
    >>> c.add_fp_consts(sl.tree.struct, sl.list.fp("X"))
    >>> c
    consts(
      data={a,b},
      sl.list.loc={x,y,z},
      sl.tree.fp={X : SET(Int)})

    You can take the side-effect free union of two constant sets via +:

    >>> d = ConstantSet(sts)
    >>> d.add_loc_consts(sl.list.struct, sl.list.loc("w"))
    >>> c + d
    consts(
      data={a,b},
      sl.list.loc={w,x,y,z},
      sl.tree.fp={X : SET(Int)})
    >>> c
    consts(
      data={a,b},
      sl.list.loc={x,y,z},
      sl.tree.fp={X : SET(Int)})

    """

    def __init__(self, structs):
        self.structs = structs
        self.loc_consts = { struct : set() for struct in structs }
        self.fp_consts = { struct : set() for struct in structs }
        self.data_consts = set()

    def __repr__(self):
        set_to_str = lambda s : '{{{}}}'.format(','.join(sorted(map(str,s))))
        nonempty = {}
        for s, locs in self.loc_consts.items():
            if locs:
                nonempty.update({s.name + '.loc' : locs})
        for s, fp in self.fp_consts.items():
            if fp:
                nonempty.update({s.name + '.fp' : fp})
        if self.data_consts:
            nonempty.update({'data' : self.data_consts})
        content = ['{}={}'.format(k, set_to_str(v))
                   for k,v in sorted(nonempty.items())]
        if len(content) > 1:
            fmt = "consts(\n  {})"
        else:
            fmt = "consts({})"
        return fmt.format(',\n  '.join(content))

    def add_data_consts(self, *consts):
        self.data_consts.update(consts)

    def add_loc_consts(self, struct, *consts):
        assert(isinstance(struct, struct_mod.Struct))
        self.loc_consts[struct].update(consts)

    def add_fp_consts(self, struct, *consts):
        assert(isinstance(struct, struct_mod.Struct))
        self.fp_consts[struct].update(consts)

    def __add__(self, other):
        # Note: This crashes if the sets differ in the structures they contain
        # This does not cause problems currently, because we always construct
        # ConstantSet instances at inner nodes from SlAst.occuring_structs()
        if not set(other.structs).issubset(self.structs):
            msg = "Trying to add constants for {} to set for {}"
            raise ValueError(msg.format(other.structs, self.structs))
        res = ConstantSet(self.structs)
        for s, consts in self.loc_consts.items():
            loc_set = set(consts)
            loc_set.update(other.loc_consts.get(s, ()))
            res.loc_consts[s] = loc_set
        for s, consts in self.fp_consts.items():
            fp_set = set(consts)
            fp_set.update(other.fp_consts.get(s, ()))
            res.fp_consts[s] = fp_set
        res.data_consts = set(self.data_consts)
        return res

    # TODO: Memoize?
    def _defined_consts(self, const_iter, z3_model):
        for c in const_iter:
            if model_utils.val_of(c, z3_model) is not None:
                yield c

    def has_consts(self, struct):
        """Does this registry contain any (location) consts of the given struct?"""
        return bool(self.loc_consts[struct])

    def defined_locs(self, struct, z3_model):
        """Generator for location consts of given struct in given model.

        No order on the returned consts guaranteed."""
        return self._defined_consts(self.loc_consts[struct], z3_model)

    def defined_data(self, z3_model):
        return self._defined_consts(self.data_consts, z3_model)

    def defined_fps(self, struct, z3_model):
        """Generator for footprint consts of given struct in given model.

        No order on the returned consts guaranteed."""
        fp_consts = (const.ref for const in self.fp_consts[struct])
        return self._defined_consts(fp_consts, z3_model)
