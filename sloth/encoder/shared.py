import collections
import operator

import z3

from ..backend import generic
from . import slast

SplitEnc = collections.namedtuple('SplitEnc', 'A B Z')

class FPVector:
    # TODO: This breaks for multi-sort backends -- if we want to keep them, that is
    def __init__(self, fp_sort, prefix, flds):
        self.fp_sort = fp_sort
        self.prefix = prefix
        self.flds = list(sorted(flds))

    def __getitem__(self, key):
        return self.fp_sort[self.prefix + key]

    def __iter__(self):
        return iter(self.flds)

    def __len__(self):
        return len(self.flds)

    def all_fps(self):
        return [self[fld] for fld in self.flds]

    def group_by_flds(self, flds):
        fld_fps = []
        other_fps = []
        for f in self:
            if f in flds:
                fld_fps.append(self[f])
            else:
                other_fps.append(self[f])
        return (fld_fps, other_fps)

    def fps_for_struct(self, struct, negate_result = False):
        for fld, fp in ((fld, self[fld]) for fld in self):
            if (fld in struct.fields) != negate_result:
                yield fp

    def fps_for_other_structs(self, struct):
        return self.fps_for_struct(struct, negate_result = True)

class DataPreds:
    def __init__(self, *preds):
        self.unary = []
        self.binary = {}
        for pred in preds:
            try:
                fld, pred = pred
            except TypeError:
                fld = None
            #assert isinstance(pred, z3.ExprRef), \
            assert isinstance(pred, slast.DataAtom), \
                    'Not a data predicate: {}'.format(pred)
            if fld is None:
                self.unary.append(pred.atom)
            else:
                self.binary.setdefault(fld, []).append(pred.atom)

    def __iter__(self):
        yield from self.unary
        for fld, preds in self.binary.items():
            for pred in preds:
                yield fld, pred

    def __str__(self):
        return ', '.join(str(p) for p in self)

    def __repr__(self):
        return 'DataPreds({})'.format(self)
