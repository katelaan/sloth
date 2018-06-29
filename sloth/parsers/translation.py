# Translation of the intermediate representation into our own SL representation

from ..encoder.slast import *
from .representation import *
from ..api import sl

class UnsupportedException(Exception):
    pass

def translate(script, filename):
    print('Translating {}...'.format(filename))
    #print(script)

    # For now we assume that acyclic list segments are the only predicate!
    try:
        stat = status(script)
        print('Status: {}'.format(stat))

        existential_dict = {}
        conjuncts = [convert(assertion.term, existential_dict = existential_dict)
                     for assertion in script.asserts]
        #print('Existentials: {}'.format(existential_dict))
        print('Conjuncts:\n - {}'.format('\n - '.join([str(c) for c in conjuncts])))
        if len(conjuncts) == 1:
            return (stat, conjuncts[0])
        elif len(conjuncts) == 2:
            return (stat, SlAnd(*conjuncts))
        else:
            raise Exception("Currently no support for >= 3 top-level assertions.")
    except UnsupportedException as e:
        print(e.args)
        return None

def status(script):
    # Extract status from something like:
        # Meta(type='set-info', content=[Attribute(kw=Keyword(str=':status'), av=AttributeValue(v=Symbol(str='unsat')))])
    status_it = (info for info in script.meta
                 if info.type == 'set-info'
                 if info.content[0].kw.str == ':status')
    return next(status_it).content[0].av.v.str

def fail(op, args):
    raise UnsupportedException('No support for {}'.format(op))

def qualIdentToPtrTerm(qi):
    try:
        # The identifier is a Symbol
        return sl.list.loc(qi.str)
    except:
        if isinstance(qi, list):
            assert len(qi) == 2
            return qualIdentToPtrTerm(qi[1])
        else:
            assert isinstance(qi, QualifiedIdentifier), 'Received {} of type {}'.format(qi, type(qi))
            assert qi.id.str == 'nil'
            return sl.list.null

SpatialTypes = {SepCon, PointsToSingleField, SpatialEq, PredCall}

def convertAnd(args, under_negation, existential_dict):
    converted = [convert(arg, under_negation, existential_dict) for arg in args]
    if all((type(arg) in SpatialTypes for arg in converted)):
        # Symbolic heap case => Rewrite conjunction into separating conjunction to ensure the desired semantics
        return SepCon.fromList(converted)
    else:
        print('That case: {}'.format([type(arg) for arg in converted]))
        # Boolean closure case => Treat as and
        return SlAnd.fromList(converted)

def convert(assertion, under_negation = False, existential_dict = {}):
    t = type(assertion)
    # TODO: Move pure formulas below sepcon?
    if t == list:
        assert isinstance(assertion[0], Symbol), 'Received head {} instead of Symbol'.format(assertion[0])
        fn = assertion[0].str
        convert_fn = {
            'or': lambda args: SlOr.fromList([convert(arg, under_negation, existential_dict) for arg in args]),
            'and': lambda args: convertAnd(args, under_negation, existential_dict),
            'not': lambda args: SlNot(convert(args[0], under_negation, existential_dict)),
            'sep': lambda args: SepCon.fromList([convert(arg, under_negation, existential_dict) for arg in args]),
            'wand': lambda args: fail('wand', args),
            'pto': lambda args: PointsToSingleField(sl.list.struct, 'next', qualIdentToPtrTerm(args[0]), qualIdentToPtrTerm(args[1])),
            'distinct': lambda args: SpatialEq(sl.list.struct, True, qualIdentToPtrTerm(args[0]), qualIdentToPtrTerm(args[1])),
            '=': lambda args: SpatialEq(sl.list.struct, False, qualIdentToPtrTerm(args[0]), qualIdentToPtrTerm(args[1])),
            'ls': lambda args: PredCall(sl.list.struct, None, None, qualIdentToPtrTerm(args[0]), qualIdentToPtrTerm(args[1]))
        }
        return convert_fn[fn](assertion[1:])

    elif t == IndexedIdentifier:
        assert assertion.s.str == 'emp', 'Unsupported indexed identifier {}'.format(assertion)
        # No direct support for emp => return (null = null) instead
        return SpatialEq(sl.list.struct, False, sl.list.null, sl.list.null)
    elif t == QualifiedIdentifier:
        assert assertion.id.str == 'emp', 'Unsupported qualified identifier {}'.format(assertion)
        # No direct support for emp => return (null = null) instead
        return SpatialEq(sl.list.struct, False, sl.list.null, sl.list.null)
    elif t == Exists:
        # All benchmarks in the divisions we participate in are quantifier free. No support necessary.
        raise UnsupportedException('No support for quantifiers')
        # if under_negation:
        #     raise UnsupportedException('No support for universal quantifiers')
        # # Detect existential quantifiers inside of negation: We don't have support for universal quantifiers, so we'd have to drop those!
        # else:
        #     for v in assertion.vars:
        #         if v in existential_dict:
        #             raise UnsupportedException('No support for reuse of bound variable identifiers')
        #         else:
        #             existential_dict[v] = v
        #     return convert(assertion.term, under_negation, existential_dict)

    else:
        raise UnsupportedException('No support for {} of type {}'.format(assertion, t))
