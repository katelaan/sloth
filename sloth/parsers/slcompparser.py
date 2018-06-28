import sys

from antlr4 import *
from antlr4.tree.Trees import Trees

from ..utils import utils
from .SLComp18Lexer import SLComp18Lexer
from .SLComp18Parser import SLComp18Parser
from .SLComp18Visitor import SLComp18Visitor
from . import translation

SlCompPaths = [
    'slcomp/qf_shls_sat',
    'slcomp/qf_shls_entl',
    'slcomp/qf_bsl_sat'
]

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
    representation = SLComp18Visitor().visitStart(tree)
    return translation.translate(representation)

def parse_successful(filename):
    #_, tree = file_to_ast(filename)
    tree = file_to_ast(filename)
    if tree.parser.getNumberOfSyntaxErrors() != 0:
        return False
    else:
        try:
            visited = SLComp18Visitor().visitStart(tree)
            slast = translation.translate(visited)
        except Exception as e:
            print('Exception: {}'.format(e))
            return False
        else:
            return True

def test_parse_all_benchmarks():
    failed = []
    for path in SlCompPaths:
        for bm in utils.collect_smt2_files(path):
            if not (bm.endswith('info') or bm.endswith('logic.smt2')):
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
    print(argv)
    try:
        bm = argv[1]
    except:
        test_parse_all_benchmarks()
    else:
        slast = parse_file(bm)

if __name__ == '__main__':
    main(sys.argv)
