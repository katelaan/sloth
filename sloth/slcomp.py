import sys

from . import api
from .utils import utils
from .encoder.slast import SlAst
from .parsers import slcompparser

SlCompPaths = [
    'slcomp/qf_shls_sat',
    'slcomp/qf_shls_entl',
    'slcomp/qf_bsl_sat'
]

def test_parse_all_benchmarks():
    failed = []
    for path in SlCompPaths:
        for bm in utils.collect_smt2_files(path):
            if not (bm.endswith('info') or bm.endswith('logic.smt2')):
                #print('Will parse {}...'.format(bm))
                if slcompparser.parse_successful(bm):
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

def check_all_benchmarks():
    failed = []
    for path in SlCompPaths:
        for bm in utils.collect_smt2_files(path):
            if not (bm.endswith('info') or bm.endswith('logic.smt2')):
                try:
                    check(*slcompparser.parse_file(bm))
                    print('Success on: {}'.format(bm))
                except:
                    print('Failed on: {}'.format(bm))
                    failed.append(bm)
    print('Finished checks.')
    if failed:
        print('Unexpected results for the following {} benchmarks:'.format(len(failed)))
        for bm in failed:
            print(bm)
    else:
        print('All checks succeeded')

def solve(slast):
    if not isinstance(slast, SlAst):
        return 'unknown'
    else:
        # Run solver...
        if api.is_sat(slast):
            return 'sat'
        else:
            return 'unsat'

def check(status, slast):
    result = solve(slast)
    if result != 'unknown' and status != 'unknown' and status != result:
        raise Exception('Unexpected solver result')
    else:
        print('OK')

def main(argv):
    try:
        mode = argv[1]
        bm = argv[2]
    except:
        if len(argv) > 1 and mode == 'checkall':
            print('Will check all benchmarks...')
            check_all_benchmarks()
        else:
            print('Will parse all benchmarks...')
            test_parse_all_benchmarks()
    else:
        (status, slast) = slcompparser.parse_file(bm)
        if mode == 'parse':
            print('Parse result:\n{}'.format(slast))
        elif mode == 'check':
            check(status, slast)
        else:
            result = solve(slast)
            print('Expected result: {}'.format(status))
            print('Actual result: {}'.format(result))

if __name__ == '__main__':
    main(sys.argv)
