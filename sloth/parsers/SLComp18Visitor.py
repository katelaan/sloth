# Generated from SLComp18.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .SLComp18Parser import SLComp18Parser
else:
    from SLComp18Parser import SLComp18Parser

# This class defines a complete generic visitor for a parse tree produced by SLComp18Parser.

class SLComp18Visitor(ParseTreeVisitor):

    # Visit a parse tree produced by SLComp18Parser#start.
    def visitStart(self, ctx:SLComp18Parser.StartContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#response.
    def visitResponse(self, ctx:SLComp18Parser.ResponseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#generalReservedWord.
    def visitGeneralReservedWord(self, ctx:SLComp18Parser.GeneralReservedWordContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#simpleSymbol.
    def visitSimpleSymbol(self, ctx:SLComp18Parser.SimpleSymbolContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#quotedSymbol.
    def visitQuotedSymbol(self, ctx:SLComp18Parser.QuotedSymbolContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#predefSymbol.
    def visitPredefSymbol(self, ctx:SLComp18Parser.PredefSymbolContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#predefKeyword.
    def visitPredefKeyword(self, ctx:SLComp18Parser.PredefKeywordContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#symbol.
    def visitSymbol(self, ctx:SLComp18Parser.SymbolContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#numeral.
    def visitNumeral(self, ctx:SLComp18Parser.NumeralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#decimal.
    def visitDecimal(self, ctx:SLComp18Parser.DecimalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#hexadecimal.
    def visitHexadecimal(self, ctx:SLComp18Parser.HexadecimalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#binary.
    def visitBinary(self, ctx:SLComp18Parser.BinaryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#string.
    def visitString(self, ctx:SLComp18Parser.StringContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#keyword.
    def visitKeyword(self, ctx:SLComp18Parser.KeywordContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#spec_constant.
    def visitSpec_constant(self, ctx:SLComp18Parser.Spec_constantContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#s_expr.
    def visitS_expr(self, ctx:SLComp18Parser.S_exprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#index.
    def visitIndex(self, ctx:SLComp18Parser.IndexContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#identifier.
    def visitIdentifier(self, ctx:SLComp18Parser.IdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#attribute_value.
    def visitAttribute_value(self, ctx:SLComp18Parser.Attribute_valueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#attribute.
    def visitAttribute(self, ctx:SLComp18Parser.AttributeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#sort.
    def visitSort(self, ctx:SLComp18Parser.SortContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#qual_identifer.
    def visitQual_identifer(self, ctx:SLComp18Parser.Qual_identiferContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#var_binding.
    def visitVar_binding(self, ctx:SLComp18Parser.Var_bindingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#sorted_var.
    def visitSorted_var(self, ctx:SLComp18Parser.Sorted_varContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#pattern.
    def visitPattern(self, ctx:SLComp18Parser.PatternContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#match_case.
    def visitMatch_case(self, ctx:SLComp18Parser.Match_caseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#term.
    def visitTerm(self, ctx:SLComp18Parser.TermContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#sort_symbol_decl.
    def visitSort_symbol_decl(self, ctx:SLComp18Parser.Sort_symbol_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#meta_spec_constant.
    def visitMeta_spec_constant(self, ctx:SLComp18Parser.Meta_spec_constantContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#fun_symbol_decl.
    def visitFun_symbol_decl(self, ctx:SLComp18Parser.Fun_symbol_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#par_fun_symbol_decl.
    def visitPar_fun_symbol_decl(self, ctx:SLComp18Parser.Par_fun_symbol_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#theory_attribute.
    def visitTheory_attribute(self, ctx:SLComp18Parser.Theory_attributeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#theory_decl.
    def visitTheory_decl(self, ctx:SLComp18Parser.Theory_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#logic_attribue.
    def visitLogic_attribue(self, ctx:SLComp18Parser.Logic_attribueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#logic.
    def visitLogic(self, ctx:SLComp18Parser.LogicContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#sort_dec.
    def visitSort_dec(self, ctx:SLComp18Parser.Sort_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#selector_dec.
    def visitSelector_dec(self, ctx:SLComp18Parser.Selector_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#constructor_dec.
    def visitConstructor_dec(self, ctx:SLComp18Parser.Constructor_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#datatype_dec.
    def visitDatatype_dec(self, ctx:SLComp18Parser.Datatype_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#function_dec.
    def visitFunction_dec(self, ctx:SLComp18Parser.Function_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#function_def.
    def visitFunction_def(self, ctx:SLComp18Parser.Function_defContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#prop_literal.
    def visitProp_literal(self, ctx:SLComp18Parser.Prop_literalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#script.
    def visitScript(self, ctx:SLComp18Parser.ScriptContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_assert.
    def visitCmd_assert(self, ctx:SLComp18Parser.Cmd_assertContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_checkSat.
    def visitCmd_checkSat(self, ctx:SLComp18Parser.Cmd_checkSatContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_checkUnsat.
    def visitCmd_checkUnsat(self, ctx:SLComp18Parser.Cmd_checkUnsatContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_checkSatAssuming.
    def visitCmd_checkSatAssuming(self, ctx:SLComp18Parser.Cmd_checkSatAssumingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_declareConst.
    def visitCmd_declareConst(self, ctx:SLComp18Parser.Cmd_declareConstContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_declareDatatype.
    def visitCmd_declareDatatype(self, ctx:SLComp18Parser.Cmd_declareDatatypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_declareDatatypes.
    def visitCmd_declareDatatypes(self, ctx:SLComp18Parser.Cmd_declareDatatypesContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_declareFun.
    def visitCmd_declareFun(self, ctx:SLComp18Parser.Cmd_declareFunContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_declareHeap.
    def visitCmd_declareHeap(self, ctx:SLComp18Parser.Cmd_declareHeapContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_declareSort.
    def visitCmd_declareSort(self, ctx:SLComp18Parser.Cmd_declareSortContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_defineFun.
    def visitCmd_defineFun(self, ctx:SLComp18Parser.Cmd_defineFunContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_defineFunRec.
    def visitCmd_defineFunRec(self, ctx:SLComp18Parser.Cmd_defineFunRecContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_defineFunsRec.
    def visitCmd_defineFunsRec(self, ctx:SLComp18Parser.Cmd_defineFunsRecContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_defineSort.
    def visitCmd_defineSort(self, ctx:SLComp18Parser.Cmd_defineSortContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_echo.
    def visitCmd_echo(self, ctx:SLComp18Parser.Cmd_echoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_exit.
    def visitCmd_exit(self, ctx:SLComp18Parser.Cmd_exitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getAssertions.
    def visitCmd_getAssertions(self, ctx:SLComp18Parser.Cmd_getAssertionsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getAssignment.
    def visitCmd_getAssignment(self, ctx:SLComp18Parser.Cmd_getAssignmentContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getInfo.
    def visitCmd_getInfo(self, ctx:SLComp18Parser.Cmd_getInfoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getModel.
    def visitCmd_getModel(self, ctx:SLComp18Parser.Cmd_getModelContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getOption.
    def visitCmd_getOption(self, ctx:SLComp18Parser.Cmd_getOptionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getProof.
    def visitCmd_getProof(self, ctx:SLComp18Parser.Cmd_getProofContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getUnsatAssumptions.
    def visitCmd_getUnsatAssumptions(self, ctx:SLComp18Parser.Cmd_getUnsatAssumptionsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getUnsatCore.
    def visitCmd_getUnsatCore(self, ctx:SLComp18Parser.Cmd_getUnsatCoreContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_getValue.
    def visitCmd_getValue(self, ctx:SLComp18Parser.Cmd_getValueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_pop.
    def visitCmd_pop(self, ctx:SLComp18Parser.Cmd_popContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_push.
    def visitCmd_push(self, ctx:SLComp18Parser.Cmd_pushContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_reset.
    def visitCmd_reset(self, ctx:SLComp18Parser.Cmd_resetContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_resetAssertions.
    def visitCmd_resetAssertions(self, ctx:SLComp18Parser.Cmd_resetAssertionsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_setInfo.
    def visitCmd_setInfo(self, ctx:SLComp18Parser.Cmd_setInfoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_setLogic.
    def visitCmd_setLogic(self, ctx:SLComp18Parser.Cmd_setLogicContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#cmd_setOption.
    def visitCmd_setOption(self, ctx:SLComp18Parser.Cmd_setOptionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#heap_dec.
    def visitHeap_dec(self, ctx:SLComp18Parser.Heap_decContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#command.
    def visitCommand(self, ctx:SLComp18Parser.CommandContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#b_value.
    def visitB_value(self, ctx:SLComp18Parser.B_valueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#option.
    def visitOption(self, ctx:SLComp18Parser.OptionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#info_flag.
    def visitInfo_flag(self, ctx:SLComp18Parser.Info_flagContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#error_behaviour.
    def visitError_behaviour(self, ctx:SLComp18Parser.Error_behaviourContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#reason_unknown.
    def visitReason_unknown(self, ctx:SLComp18Parser.Reason_unknownContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#model_response.
    def visitModel_response(self, ctx:SLComp18Parser.Model_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#info_response.
    def visitInfo_response(self, ctx:SLComp18Parser.Info_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#valuation_pair.
    def visitValuation_pair(self, ctx:SLComp18Parser.Valuation_pairContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#t_valuation_pair.
    def visitT_valuation_pair(self, ctx:SLComp18Parser.T_valuation_pairContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#check_sat_response.
    def visitCheck_sat_response(self, ctx:SLComp18Parser.Check_sat_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#echo_response.
    def visitEcho_response(self, ctx:SLComp18Parser.Echo_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_assertions_response.
    def visitGet_assertions_response(self, ctx:SLComp18Parser.Get_assertions_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_assignment_response.
    def visitGet_assignment_response(self, ctx:SLComp18Parser.Get_assignment_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_info_response.
    def visitGet_info_response(self, ctx:SLComp18Parser.Get_info_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_model_response.
    def visitGet_model_response(self, ctx:SLComp18Parser.Get_model_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_option_response.
    def visitGet_option_response(self, ctx:SLComp18Parser.Get_option_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_proof_response.
    def visitGet_proof_response(self, ctx:SLComp18Parser.Get_proof_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_unsat_assump_response.
    def visitGet_unsat_assump_response(self, ctx:SLComp18Parser.Get_unsat_assump_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_unsat_core_response.
    def visitGet_unsat_core_response(self, ctx:SLComp18Parser.Get_unsat_core_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#get_value_response.
    def visitGet_value_response(self, ctx:SLComp18Parser.Get_value_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#specific_success_response.
    def visitSpecific_success_response(self, ctx:SLComp18Parser.Specific_success_responseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SLComp18Parser#general_response.
    def visitGeneral_response(self, ctx:SLComp18Parser.General_responseContext):
        return self.visitChildren(ctx)



del SLComp18Parser