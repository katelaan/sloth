from antlr4 import *
from antlr4.tree.Trees import Trees

from .SLComp18Lexer import SLComp18Lexer
from .SLComp18Parser import SLComp18Parser
from .SLComp18Visitor import SLComp18Visitor
from . import translation
from ..encoder.slast import SlAst

def file_to_ast(filename):
    input = FileStream(filename, encoding='utf8')
    lexer = SLComp18Lexer(input)
    stream = CommonTokenStream(lexer)
    parser = SLComp18Parser(stream)
    #return parser, parser.start()
    return parser.start()

def parse_file(filename):
    #parser, tree = file_to_ast(filename)
    tree = file_to_ast(filename)
    #print(Trees.toStringTree(tree, None, tree.parser))
    representation = SLComp18Visitor().visitStart(tree)
    return translation.translate(representation, filename)

def parse_successful(filename):
    #_, tree = file_to_ast(filename)
    tree = file_to_ast(filename)
    if tree.parser.getNumberOfSyntaxErrors() != 0:
        return False
    else:
        try:
            visited = SLComp18Visitor().visitStart(tree)
            (status, slast) = translation.translate(visited, filename)
            if not isinstance(slast, SlAst):
                raise Exception('Parse result of wrong type: {}'.format(slast))
        except Exception as e:
            print('Exception: {}'.format(e))
            return False
        else:
            return True
