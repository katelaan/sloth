# Generated from SLComp18.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .SLComp18Parser import SLComp18Parser
else:
    from SLComp18Parser import SLComp18Parser

# This class defines a complete generic visitor for a parse tree produced by SLComp18Parser.

from collections import namedtuple as nt
from functools import partial
from itertools import groupby

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

def cmd_not_supported(cmd, args):
    raise NotImplementedError('No support for {}'.format(cmd))

def no_support(cmd):
    return partial(cmd_not_supported, cmd)

def declare_datatypes(args):
    it = groupby(args, key = lambda arg: isinstance(arg, SortDecl))
    decls = list(next(it))
    terms = list(next(it))
    assert len(decls) == len(terms)
    return [DataTypeDecl(*pair) for pair in zip(decls, terms)]

def declare_heap(args):
    return HeapDecl({
        decl_pair[0]: decl_pair[1]
        for decl_pair in args
    })

def define_funs_rec(args):
    it = groupby(args, key = lambda arg: isinstance(arg, FunDecl))
    decls = list(next(it))
    terms = list(next(it))
    assert len(decls) == len(terms)
    return [FunDef(*pair) for pair in zip(decls, terms)]

cmdTypeToCmd = {
    'assert': lambda args: Assert(args[0]),
    'check-sat': lambda _: Task('check-sat', []),
    'check-sat-assuming': no_support('check-sat-assuming'),
    'check-sat': lambda _: Task('check-unsat', []),
    'declare-const': lambda args: ConstDecl(*args),
    'declare-fun': no_support('declare-fun'),
    'declare-datatype': lambda args: [SortDecl(args[0], 0), args[1]],
    'declare-datatypes': declare_datatypes,
    'declare-heap': declare_heap,
    'declare-sort': lambda args: SortDecl(*args),
    'define-fun': no_support('define-fun'),
    'define-fun-rec': lambda args: args[0],
    'define-funs-rec': define_funs_rec,
    'define-sort': no_support('define-sort'),
    'echo': no_support('echo'),
    'exit': no_support('exit'),
    'get-assertions': no_support('get-assertions'),
    'get-assignment': no_support('get-assignment'),
    'get-info': no_support('get-info'),
    'get-model': lambda _: Task('get-model', []),
    'get-option': no_support('get-option'),
    'get-proof': no_support('get-proof'),
    'get-unsat-assumptions': no_support('get-unsat-assumptions'),
    'get-unsat-core': no_support('get-unsat-core'),
    'get-value': no_support('get-value'),
    'pop': no_support('pop'),
    'push': no_support('push'),
    'reset': no_support('reset'),
    'reset-assertions': no_support('reset-assertions'),
    'set-info':  lambda args: Meta('set-info', args),
    'set-logic': lambda args: Meta('set-logic', args),
    'set-option': no_support('set-option'),
}


class SLComp18Visitor(ParseTreeVisitor):

    def aggregateResult(self, aggregate, nextResult):
        if aggregate is None:
            return nextResult
        elif nextResult is None:
            return aggregate
        elif isinstance(aggregate, list):
            return aggregate + [nextResult]
        else:
            return [aggregate, nextResult]

    def fail(self, ctx):
        print('Text: {}'.format(ctx.getText))
        print('Children: {}'.format(visitChildren(ctx)))
        raise NotImplementedError()

    # Visit a parse tree produced by SLComp18Parser#start.
    def visitStart(self, ctx:SLComp18Parser.StartContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SLComp18Parser#response.
    def visitResponse(self, ctx:SLComp18Parser.ResponseContext):
        self.fail(ctx)

    # Visit a parse tree produced by SLComp18Parser#generalReservedWord.
    def visitGeneralReservedWord(self, ctx:SLComp18Parser.GeneralReservedWordContext):
        self.fail(ctx)

    # Visit a parse tree produced by SLComp18Parser#simpleSymbol.
    def visitSimpleSymbol(self, ctx:SLComp18Parser.SimpleSymbolContext):
        return Symbol(ctx.getText())


    # Visit a parse tree produced by SLComp18Parser#quotedSymbol.
    def visitQuotedSymbol(self, ctx:SLComp18Parser.QuotedSymbolContext):
        return Symbol(ctx.getText())


    # Visit a parse tree produced by SLComp18Parser#predefSymbol.
    def visitPredefSymbol(self, ctx:SLComp18Parser.PredefSymbolContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#predefKeyword.
    def visitPredefKeyword(self, ctx:SLComp18Parser.PredefKeywordContext):
        return Keyword(ctx.getText())


    # Visit a parse tree produced by SLComp18Parser#symbol.
    def visitSymbol(self, ctx:SLComp18Parser.SymbolContext):
        # Just propagate the simple/quoted symbol constructed from the children
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#numeral.
    def visitNumeral(self, ctx:SLComp18Parser.NumeralContext):
        return int(ctx.getText())


    # Visit a parse tree produced by SLComp18Parser#decimal.
    def visitDecimal(self, ctx:SLComp18Parser.DecimalContext):
        return float(ctx.getText())


    # Visit a parse tree produced by SLComp18Parser#hexadecimal.
    def visitHexadecimal(self, ctx:SLComp18Parser.HexadecimalContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#binary.
    def visitBinary(self, ctx:SLComp18Parser.BinaryContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#string.
    def visitString(self, ctx:SLComp18Parser.StringContext):
        return ctx.getText()


    # Visit a parse tree produced by SLComp18Parser#keyword.
    def visitKeyword(self, ctx:SLComp18Parser.KeywordContext):
        #  Avoid another level of wrapping by propagating predefined keywords
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#spec_constant.
    def visitSpec_constant(self, ctx:SLComp18Parser.Spec_constantContext):
        return Constant(self.visitChildren(ctx))


    # Visit a parse tree produced by SLComp18Parser#s_expr.
    def visitS_expr(self, ctx:SLComp18Parser.S_exprContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#index.
    def visitIndex(self, ctx:SLComp18Parser.IndexContext):
        # Just pass on the symbol/index rather than introducing another level of wrapping
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#identifier.
    def visitIdentifier(self, ctx:SLComp18Parser.IdentifierContext):
        child_res = self.visitChildren(ctx)
        is_indexed = False
        try:
            is_indexed = len(child_res) >= 2
        except:
            pass

        if is_indexed:
            return IndexedIdentifier(child_res[0], child_res[1:])
        else:
            assert isinstance(child_res, Symbol)
            return child_res


    # Visit a parse tree produced by SLComp18Parser#attribute_value.
    def visitAttribute_value(self, ctx:SLComp18Parser.Attribute_valueContext):
        child_res = self.visitChildren(ctx)
        assert type(child_res) in (Symbol, Constant)
        return AttributeValue(child_res)


    # Visit a parse tree produced by SLComp18Parser#attribute.
    def visitAttribute(self, ctx:SLComp18Parser.AttributeContext):
        return Attribute(*self.visitChildren(ctx))


    # Visit a parse tree produced by SLComp18Parser#sort.
    def visitSort(self, ctx:SLComp18Parser.SortContext):
        child_res = self.visitChildren(ctx)
        assert isinstance(child_res, Symbol), \
            "Received {} of type {} instead of Symbol".format(child_res, type(child_res))
        return Sort(child_res)


    # Visit a parse tree produced by SLComp18Parser#qual_identifer.
    def visitQual_identifer(self, ctx:SLComp18Parser.Qual_identiferContext):
        child_res = self.visitChildren(ctx)
        try:
            return QualifiedIdentifier(*child_res)
        except:
            assert type(child_res) in (Symbol, IndexedIdentifier), \
                "Received {} of type {} instead of Symbol/IndexedIdentifier".format(child_res, type(child_res))
            return child_res


    # Visit a parse tree produced by SLComp18Parser#var_binding.
    def visitVar_binding(self, ctx:SLComp18Parser.Var_bindingContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#sorted_var.
    def visitSorted_var(self, ctx:SLComp18Parser.Sorted_varContext):
        return SortedVar(*self.visitChildren(ctx))


    # Visit a parse tree produced by SLComp18Parser#pattern.
    def visitPattern(self, ctx:SLComp18Parser.PatternContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#match_case.
    def visitMatch_case(self, ctx:SLComp18Parser.Match_caseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#term.
    def visitTerm(self, ctx:SLComp18Parser.TermContext):
        #child = ctx.getChild(1)
        #if child:
        try:
            child = cts.getChild(1)
        except:
            return self.visitChildren(ctx)
        else:
            txt = child.getText()
            if txt == 'exists':
                child_res = self.visitChildren(ctx)
                vars_ = child_res[:-1]
                term = child_res[-1]
                return Exists(vars_, term)
            elif txt == 'forall':
                raise NotImplementedError()
            elif txt == '!':
                raise NotImplementedError()
            elif txt == 'match':
                raise NotImplementedError()
            else:
                return self.visitChildren(ctx)

    # Visit a parse tree produced by SLComp18Parser#sort_symbol_decl.
    def visitSort_symbol_decl(self, ctx:SLComp18Parser.Sort_symbol_declContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#meta_spec_constant.
    def visitMeta_spec_constant(self, ctx:SLComp18Parser.Meta_spec_constantContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#fun_symbol_decl.
    def visitFun_symbol_decl(self, ctx:SLComp18Parser.Fun_symbol_declContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#par_fun_symbol_decl.
    def visitPar_fun_symbol_decl(self, ctx:SLComp18Parser.Par_fun_symbol_declContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#theory_attribute.
    def visitTheory_attribute(self, ctx:SLComp18Parser.Theory_attributeContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#theory_decl.
    def visitTheory_decl(self, ctx:SLComp18Parser.Theory_declContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#logic_attribue.
    def visitLogic_attribue(self, ctx:SLComp18Parser.Logic_attribueContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#logic.
    def visitLogic(self, ctx:SLComp18Parser.LogicContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#sort_dec.
    def visitSort_dec(self, ctx:SLComp18Parser.Sort_decContext):
        return SortDecl(*self.visitChildren(ctx))


    # Visit a parse tree produced by SLComp18Parser#selector_dec.
    def visitSelector_dec(self, ctx:SLComp18Parser.Selector_decContext):
        return Selector(*self.visitChildren(ctx))


    # Visit a parse tree produced by SLComp18Parser#constructor_dec.
    def visitConstructor_dec(self, ctx:SLComp18Parser.Constructor_decContext):
        child_res = self.visitChildren(ctx)
        return ConstructorDecl(child_res[0], child_res[1:], None)


    # Visit a parse tree produced by SLComp18Parser#datatype_dec.
    def visitDatatype_dec(self, ctx:SLComp18Parser.Datatype_decContext):
        # The datatype will be assembled in the visitors for declare-datatype(s)
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#function_dec.
    def visitFunction_dec(self, ctx:SLComp18Parser.Function_decContext):
        child_res = self.visitChildren(ctx)
        return FunDecl(child_res[0], child_res[1:-1], child_res[-1])


    # Visit a parse tree produced by SLComp18Parser#function_def.
    def visitFunction_def(self, ctx:SLComp18Parser.Function_defContext):
        name = None
        params = []
        resultType = None
        term = None

        child_res = self.visitChildren(ctx)
        for arg in child_res:
            t = type(arg)
            if t == Symbol:
                name = arg
            elif t == SortedVar:
                params.append(arg)
            elif t == Sort:
                resultType = arg
            else:
                term = arg

        return FunDef(FunDecl(name, params, resultType), term)


    # Visit a parse tree produced by SLComp18Parser#prop_literal.
    def visitProp_literal(self, ctx:SLComp18Parser.Prop_literalContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#script.
    def visitScript(self, ctx:SLComp18Parser.ScriptContext):
        sorts = []
        types = []
        heap = None
        consts = []
        funs = []
        asserts = []
        meta = []
        tasks = []

        def process_list(args):
            nonlocal types
            if isinstance(args[0], DataTypeDecl):
                types = args
            else:
                assert isinstance(args[0], FunDef)
                funs.extend(args)

        def set_heap(arg):
            nonlocal heap
            if heap is not None:
                raise Exception('Duplicate heap declaration')
            heap = arg

        process_type = {
            SortDecl: sorts.append,
            list: process_list,
            HeapDecl: set_heap,
            ConstDecl: consts.append,
            FunDef: funs.append,
            Assert: asserts.append,
            Meta: meta.append,
            Task: tasks.append
        }

        for arg in self.visitChildren(ctx):
            process_type[type(arg)](arg)

        if heap is None:
            raise Exception('No heap declaration')
        if not asserts:
            raise Exception('No assert => Nothing to check')

        return Script(sorts, types, heap, consts, funs, asserts, meta, tasks)

    # Visit a parse tree produced by SLComp18Parser#cmd_assert.
    def visitCmd_assert(self, ctx:SLComp18Parser.Cmd_assertContext):
        return 'assert'


    # Visit a parse tree produced by SLComp18Parser#cmd_checkSat.
    def visitCmd_checkSat(self, ctx:SLComp18Parser.Cmd_checkSatContext):
        return 'check-sat'


    # Visit a parse tree produced by SLComp18Parser#cmd_checkUnsat.
    def visitCmd_checkUnsat(self, ctx:SLComp18Parser.Cmd_checkUnsatContext):
        return 'check-unsat'


    # Visit a parse tree produced by SLComp18Parser#cmd_checkSatAssuming.
    def visitCmd_checkSatAssuming(self, ctx:SLComp18Parser.Cmd_checkSatAssumingContext):
        return 'check-sat-assuming'


    # Visit a parse tree produced by SLComp18Parser#cmd_declareConst.
    def visitCmd_declareConst(self, ctx:SLComp18Parser.Cmd_declareConstContext):
        return 'declare-const'


    # Visit a parse tree produced by SLComp18Parser#cmd_declareDatatype.
    def visitCmd_declareDatatype(self, ctx:SLComp18Parser.Cmd_declareDatatypeContext):
        return 'declare-datatype'


    # Visit a parse tree produced by SLComp18Parser#cmd_declareDatatypes.
    def visitCmd_declareDatatypes(self, ctx:SLComp18Parser.Cmd_declareDatatypesContext):
        return 'declare-datatypes'


    # Visit a parse tree produced by SLComp18Parser#cmd_declareFun.
    def visitCmd_declareFun(self, ctx:SLComp18Parser.Cmd_declareFunContext):
        return 'declare-fun'


    # Visit a parse tree produced by SLComp18Parser#cmd_declareHeap.
    def visitCmd_declareHeap(self, ctx:SLComp18Parser.Cmd_declareHeapContext):
        return 'declare-heap'


    # Visit a parse tree produced by SLComp18Parser#cmd_declareSort.
    def visitCmd_declareSort(self, ctx:SLComp18Parser.Cmd_declareSortContext):
        return 'declare-sort'


    # Visit a parse tree produced by SLComp18Parser#cmd_defineFun.
    def visitCmd_defineFun(self, ctx:SLComp18Parser.Cmd_defineFunContext):
        return 'define-fun'


    # Visit a parse tree produced by SLComp18Parser#cmd_defineFunRec.
    def visitCmd_defineFunRec(self, ctx:SLComp18Parser.Cmd_defineFunRecContext):
        return 'define-fun-rec'


    # Visit a parse tree produced by SLComp18Parser#cmd_defineFunsRec.
    def visitCmd_defineFunsRec(self, ctx:SLComp18Parser.Cmd_defineFunsRecContext):
        return 'define-funs-rec'


    # Visit a parse tree produced by SLComp18Parser#cmd_defineSort.
    def visitCmd_defineSort(self, ctx:SLComp18Parser.Cmd_defineSortContext):
        return 'define-sort'


    # Visit a parse tree produced by SLComp18Parser#cmd_echo.
    def visitCmd_echo(self, ctx:SLComp18Parser.Cmd_echoContext):
        return 'echo'


    # Visit a parse tree produced by SLComp18Parser#cmd_exit.
    def visitCmd_exit(self, ctx:SLComp18Parser.Cmd_exitContext):
        return 'exit'


    # Visit a parse tree produced by SLComp18Parser#cmd_getAssertions.
    def visitCmd_getAssertions(self, ctx:SLComp18Parser.Cmd_getAssertionsContext):
        return 'get-assertions'


    # Visit a parse tree produced by SLComp18Parser#cmd_getAssignment.
    def visitCmd_getAssignment(self, ctx:SLComp18Parser.Cmd_getAssignmentContext):
        return 'get-assignment'


    # Visit a parse tree produced by SLComp18Parser#cmd_getInfo.
    def visitCmd_getInfo(self, ctx:SLComp18Parser.Cmd_getInfoContext):
        return 'get-info'


    # Visit a parse tree produced by SLComp18Parser#cmd_getModel.
    def visitCmd_getModel(self, ctx:SLComp18Parser.Cmd_getModelContext):
        return 'get-model'


    # Visit a parse tree produced by SLComp18Parser#cmd_getOption.
    def visitCmd_getOption(self, ctx:SLComp18Parser.Cmd_getOptionContext):
        return 'get-option'


    # Visit a parse tree produced by SLComp18Parser#cmd_getProof.
    def visitCmd_getProof(self, ctx:SLComp18Parser.Cmd_getProofContext):
        return 'get-proof'


    # Visit a parse tree produced by SLComp18Parser#cmd_getUnsatAssumptions.
    def visitCmd_getUnsatAssumptions(self, ctx:SLComp18Parser.Cmd_getUnsatAssumptionsContext):
        return 'get-unsat-assumptions'


    # Visit a parse tree produced by SLComp18Parser#cmd_getUnsatCore.
    def visitCmd_getUnsatCore(self, ctx:SLComp18Parser.Cmd_getUnsatCoreContext):
        return 'get-unsat-core'


    # Visit a parse tree produced by SLComp18Parser#cmd_getValue.
    def visitCmd_getValue(self, ctx:SLComp18Parser.Cmd_getValueContext):
        return 'get-value'


    # Visit a parse tree produced by SLComp18Parser#cmd_pop.
    def visitCmd_pop(self, ctx:SLComp18Parser.Cmd_popContext):
        return 'pop'


    # Visit a parse tree produced by SLComp18Parser#cmd_push.
    def visitCmd_push(self, ctx:SLComp18Parser.Cmd_pushContext):
        return 'push'


    # Visit a parse tree produced by SLComp18Parser#cmd_reset.
    def visitCmd_reset(self, ctx:SLComp18Parser.Cmd_resetContext):
        return 'reset'


    # Visit a parse tree produced by SLComp18Parser#cmd_resetAssertions.
    def visitCmd_resetAssertions(self, ctx:SLComp18Parser.Cmd_resetAssertionsContext):
        return 'reset-assertions'


    # Visit a parse tree produced by SLComp18Parser#cmd_setInfo.
    def visitCmd_setInfo(self, ctx:SLComp18Parser.Cmd_setInfoContext):
        return 'set-info'


    # Visit a parse tree produced by SLComp18Parser#cmd_setLogic.
    def visitCmd_setLogic(self, ctx:SLComp18Parser.Cmd_setLogicContext):
        return 'set-logic'


    # Visit a parse tree produced by SLComp18Parser#cmd_setOption.
    def visitCmd_setOption(self, ctx:SLComp18Parser.Cmd_setOptionContext):
        return 'set-option'


    # Visit a parse tree produced by SLComp18Parser#heap_dec.
    def visitHeap_dec(self, ctx:SLComp18Parser.Heap_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#command.
    def visitCommand(self, ctx:SLComp18Parser.CommandContext):
        child_res = self.visitChildren(ctx)
        if isinstance(child_res, str):
            return cmdTypeToCmd[child_res]([])
        else:
            cmd, *args = self.visitChildren(ctx)
            return cmdTypeToCmd[cmd](args)


    # Visit a parse tree produced by SLComp18Parser#b_value.
    def visitB_value(self, ctx:SLComp18Parser.B_valueContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#option.
    def visitOption(self, ctx:SLComp18Parser.OptionContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#info_flag.
    def visitInfo_flag(self, ctx:SLComp18Parser.Info_flagContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#error_behaviour.
    def visitError_behaviour(self, ctx:SLComp18Parser.Error_behaviourContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#reason_unknown.
    def visitReason_unknown(self, ctx:SLComp18Parser.Reason_unknownContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#model_response.
    def visitModel_response(self, ctx:SLComp18Parser.Model_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#info_response.
    def visitInfo_response(self, ctx:SLComp18Parser.Info_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#valuation_pair.
    def visitValuation_pair(self, ctx:SLComp18Parser.Valuation_pairContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#t_valuation_pair.
    def visitT_valuation_pair(self, ctx:SLComp18Parser.T_valuation_pairContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#check_sat_response.
    def visitCheck_sat_response(self, ctx:SLComp18Parser.Check_sat_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#echo_response.
    def visitEcho_response(self, ctx:SLComp18Parser.Echo_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_assertions_response.
    def visitGet_assertions_response(self, ctx:SLComp18Parser.Get_assertions_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_assignment_response.
    def visitGet_assignment_response(self, ctx:SLComp18Parser.Get_assignment_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_info_response.
    def visitGet_info_response(self, ctx:SLComp18Parser.Get_info_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_model_response.
    def visitGet_model_response(self, ctx:SLComp18Parser.Get_model_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_option_response.
    def visitGet_option_response(self, ctx:SLComp18Parser.Get_option_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_proof_response.
    def visitGet_proof_response(self, ctx:SLComp18Parser.Get_proof_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_unsat_assump_response.
    def visitGet_unsat_assump_response(self, ctx:SLComp18Parser.Get_unsat_assump_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_unsat_core_response.
    def visitGet_unsat_core_response(self, ctx:SLComp18Parser.Get_unsat_core_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_value_response.
    def visitGet_value_response(self, ctx:SLComp18Parser.Get_value_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#specific_success_response.
    def visitSpecific_success_response(self, ctx:SLComp18Parser.Specific_success_responseContext):
        self.fail(ctx)


    # Visit a parse tree produced by SLComp18Parser#general_response.
    def visitGeneral_response(self, ctx:SLComp18Parser.General_responseContext):
        self.fail(ctx)



del SLComp18Parser
