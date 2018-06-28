from collections import namedtuple as nt

# Dummy -> not needed, just return None
#CmdTypeWrapper = nt('CmdTypeWrapper', 'ct') # Not needed, just pass on the commands
# Args -> not needed, just return List

# Just return the values?
#Decimal = nt('Decimal', 'd')
#Numeral = nt('Numeral', 'i')
#StrVal = nt('StrVal', 's')
Constant = nt('Constant', 'c')

Symbol = nt('Symbol', 'str')
IndexedIdentifier = nt('IndexedIdentifier', 's ixs')
QualifiedIdentifier = nt('QualifiedIdentifier', 'id sort')

Keyword = nt('Keyword', 'str')
AttributeValue = nt('AttributeValue', 'v')
Attribute = nt('Attribute', 'kw av')

SortDecl = nt('SortDecl', 'name arity')
SortedVar = nt('SortedVar', 'name sort')

Sort = nt('Sort', 'symbol')
Selector = nt('Selector', 'sel sort')
ConstructorDecl = nt('ConstructorDecl', 'name sels params')
DataTypeDecl = nt('DataTypeDecl', 'sort constructors')
# DataTypes -> not needed, just return list

HeapDecl = nt('HeapDecl', 'mapping')

ConstDecl = nt('ConstDecl', 'name sort')
FunDecl = nt('FunDecl', 'name args ret')
FunDef = nt('FunDef', 'decl term')
#FunDefs -> not needed, just return list

Exists = nt('Exists', 'vars term')

Assert = nt('Assert', 'term')
Task = nt('Task', 'task args') # check-sat, check-unsat, get-model

Meta = nt('Meta', 'type content') # set-logic, set-info

class Script:
    def __init__(self,
                 sorts = [],
                 types = [],
                 heap = None,
                 consts = [],
                 funs = [],
                 asserts = [],
                 meta = [],
                 tasks = []):
        self.sorts = sorts
        self.types = types
        self.heap = heap
        self.consts = consts
        self.funs = funs
        self.asserts = asserts
        self.meta = meta
        self.tasks = tasks

    def __repr__(self):
        return 'Script(sorts = {!r},\n  types = {!r},\n  heap = {!r},\n  consts = {!r},\n  funs = {!r},\n  asserts = {!r},\n  meta = {!r},\n  tasks = {!r})'.format(self.sorts, self.types, self.heap, self.consts, self.funs, self.asserts, self.meta, self.tasks)
