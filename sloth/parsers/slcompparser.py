import sys

from antlr4 import *
from antlr4.tree.Trees import Trees
from .SLComp18Lexer import SLComp18Lexer
from .SLComp18Parser import SLComp18Parser
from .SLComp18Visitor import SLComp18Visitor

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
    print(Trees.toStringTree(tree, None, tree.parser))
    return SLComp18Visitor().visitStart(tree)

def parse_successful(filename):
    #_, tree = file_to_ast(filename)
    tree = file_to_ast(filename)
    return tree.parser.getNumberOfSyntaxErrors() == 0

def test_parse_all_benchmarks():
    from ..api import all_benchmarks
    failed = []
    for bm in all_benchmarks():
        if 'sl-comp' in bm:
            print('Will parse {}...'.format(bm))
            if parse_successful(bm):
                print('OK')
            else:
                print('failed')
                failed.append(bm)
    print('Finished tests.')
    if failed:
        print('The following {} benchmarks failed to parse:'.format(len(failed)))
        for bm in failed:
            print(bm)
    else:
        print('All tests succeeded')

def main(argv):
    parse_file(argv[1])

if __name__ == '__main__':
    main(sys.argv)
