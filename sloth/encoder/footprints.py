"""

.. testsetup::

   from sloth import *
   from sloth.encoder.footprints import *

"""

from ..backend import struct as struct_mod
from .utils import EncoderState
from .astutils import structs_in_ast

class FootprintManager:
    """Adapter for the dict of footprint names currently in scope.

    >>> ls, tree = sl.list.struct, sl.tree.struct
    >>> m = FootprintManager([ls, tree], 'x')
    >>> m.get_fp(ls, "next")
    'XN'
    >>> m.get_fp(tree, "left")
    'XL'
    >>> mr = m.follow_pointer(tree, "right")
    >>> (mr.get_fp(ls, "next"), mr.get_fp(tree, "left"), mr.get_fp(tree, "right"))
    ('XN', 'XRr', 'XRr')

    """

    def __init__(self, structs, root, fp_dict = None):
        self.structs = structs
        self.root = root
        if fp_dict is None:
            self.fp_dict = FootprintManager.default_fp_dict(structs, root)
        else:
            self.fp_dict = fp_dict

    def get_fp(self, struct, fld):
        return self.fp_dict[(struct, fld)]

    def typed_fp_dict(self):
        return { (s,f) : s.fp_sort[v] for (s,f), v in self.fp_dict.items() }

    def follow_pointer(self, struct, fld):
        new_dict = dict(self.fp_dict)
        new_dict.update({(struct, any_field) : self.get_fp(struct, fld) + fld[0]
                         for any_field in struct.fields })
        return FootprintManager(self.structs, self.root, new_dict)

    def extend_root(self, suffix):
        return FootprintManager(self.structs, self.root + suffix, dict(self.fp_dict))

    def all_fps(self):
        return self.typed_fp_dict().values()

    @staticmethod
    def fp_id(struct, fld, root):
        assert(isinstance(struct, struct_mod.Struct))
        assert(isinstance(fld, str))
        assert(isinstance(root, str))
        return (root + fld[0]).upper()
        #return (struct.unqualified_name[0] + root + fld[0]).upper()

    @staticmethod
    def default_fp_dict(structs, root):
        return { (s,f) : FootprintManager.fp_id(s, f, root)
                         for s in structs
                         for f in s.fields }

def make_fp(struct, fld, root):
    return struct.fp_sort[FootprintManager.fp_id(struct, fld, str(root))]

def make_global_fps(obj, *child_encs):
    global_dict = FootprintManager(structs_in_ast(obj), obj.fp_letter + str(obj.id_) + "__").typed_fp_dict()
    local_dicts = [child.fps for child in obj]
    for l in local_dicts:
        # Make sure we're not passing FootprintManagers around
        assert(isinstance(l, dict))
    # Restrict to the fields that actually occur under the operator
    global_dict = { k : v for k,v in global_dict.items()
                    if any((k in d) for d in local_dicts) }
    return global_dict

def to_fp_dict(fps):
    if fps is None:
        return None
    try:
        return fps.typed_fp_dict()
    except AttributeError:
        assert isinstance(fps, dict)
        return fps
