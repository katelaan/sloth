"""General utility classes and functions.

.. testsetup::

   from sloth.utils.utils import *

"""

import os
from os.path import isfile, isdir, join
import sys
import contextlib

from .. import config

class SlothException(Exception):
    """Root exception"""

class IllegalSolverState(SlothException):
    """Unexpected state reached => Probably bug in our solver"""

def wrong_type(obj):
    return 'Received argument {} of unsupported type {}'.format(obj, type(obj).__name__)

def merge_dicts(*zs):
    """Merge one or more dictionaries into one without modifying any argument dict

    In case of duplicate keys, values may be accidentally overridden.

    >>> merge_dicts({1:10,2:20}, {3:30}, {4:40})
    {1: 10, 2: 20, 3: 30, 4: 40}
    >>> merge_dicts({1:10,2:20}, {1:21}, {1:23})
    {1: 23, 2: 20}

    """
    res = {}
    for z in zs:
        res.update(z)
    return res

def merge_sets(*zs):
    """Merge one or more sets into one without modifying any argument set.

    >>> merge_sets(set([1,2,3]), set([3,4,5]))
    {1, 2, 3, 4, 5}

    """
    res = set()
    for z in zs:
        res.update(z)
    return res

def zip_with_const(it, c):
    for elem in it:
        yield (elem, c)

def flatten(xss):
    return [x for xs in xss for x in xs]

def find_first(p, seq):
    """Returns the first item in `seq` that satisies `p`"""
    try:
        return next(x for x in seq if p(x))
    except StopIteration:
        msg = "{} doesn't contain any value satisfying the predicate."
        raise ValueError(msg.format(seq))

def seq_exists(p, seq):
    """Returns True iff sequence contains item such that p(item) == True."""
    for item in seq:
        if p(item):
            return True
    return False

def consecutive_pairs(it):
    """Yield all (overlapping) conseuctive pairs from the iterable.

    >>> list(consecutive_pairs(range(5)))
    [(0, 1), (1, 2), (2, 3), (3, 4)]

    """
    it = iter(it)
    try:
        fst = next(it)
        snd = next(it)
    except:
        # Fewer than two elements => No pairs to yield
        pass
    else:
        yield (fst, snd)
        try:
            while True:
                fst = snd
                snd = next(it)
                yield (fst, snd)
        except StopIteration:
            pass

def contains_all(substrings, string):
        for s in substrings:
            if s not in string:
                return False
        return True

class DummyFile:
    def write(self, x): pass

@contextlib.contextmanager
def nostdout():
    """Context manager for suppressing all output to stdout"""
    save_stdout = sys.stdout
    sys.stdout = DummyFile()
    try:
        yield
    except Exception as e:
        sys.stdout = save_stdout
        #print("RERAISING")
        raise e
    sys.stdout = save_stdout

def collect_smt2_files(path, dir_whitelist = None):
    """Recursively collects the paths to all .smt2 files in whitelisted directories,
    starting from the given path; if dir_whitelist is None (default), collects all
    .smt2 files.

    Returns sorted list of (relative) paths to all found benchmarks."""
    # Skip files in the benchmarks dir itself if we're in whitelist mode
    if dir_whitelist is None or path != config.BENCHMARK_PATH or path in dir_whitelist:
        local_files = [join(path,f) for f in os.listdir(path)
                       if isfile(join(path, f))
                       if "smt2" in f]
    else:
        local_files = []
    # Collect files from whitelisted subdirectories (or all, if no whitelist given)
    dirs = [join(path, d) for d in os.listdir(path)
            if isdir(join(path, d))
            if (True if dir_whitelist is None else d in dir_whitelist)]
    recursive_files = [files for d in dirs
                       for files in collect_smt2_files(d, dir_whitelist)]

    all_files = local_files + recursive_files
    return sorted(all_files)

@contextlib.contextmanager
def stats(fields):
    """Context manager for logging statistics"""
    d = {f : [] for f in fields}
    yield d
    total = sum(map(len,d.values()))
    for f, f_desc in fields.items():
        print("Number of {}: {}/{}".format(f_desc, len(d[f]), total))
        if d[f]:
            print(" * " + "\n * ".join(d[f]))

def indented(lines, indent = 2):
    indented_lines = [" "*indent + line for line in lines.split("\n")]
    return "\n".join(indented_lines)

def lineify(string, split_at, max_len = 80):
    lines = []
    tokens = string.split(split_at)
    curr = ""
    while tokens:
        token = tokens[0]
        if (len(curr) + len(split_at) + len(token) <= max_len) or len(curr) == 0:
            curr += split_at + token
            tokens = tokens[1:]
        else:
            # Strip leading split_at
            lines.append(curr[len(split_at):])
            curr = ""
    # Add last line
    if curr:
        lines.append(curr[len(split_at):])
    return "\n".join(lines)

def unique_repr(obj):
    """Return a deterministic representation of the given object.

    >>> unique_repr({'b','a','ab','c'})
    "{'a', 'ab', 'b', 'c'}"
    >>> unique_repr({3: {5,4}, 8: {3,6,0}})
    '{3: {4, 5}, 8: {0, 3, 6}}'

    """
    if isinstance(obj, dict):
        sorted_dict_reprs = sorted(unique_repr(k) + ': ' + unique_repr(v)
                                   for k,v in obj.items())
        return '{' + ', '.join(sorted_dict_reprs) + '}'
    if isinstance(obj, set):
        return '{' + ', '.join(sorted(unique_repr(elem) for elem in obj)) + '}'
    else:
        return repr(obj)

def print_unique_repr(obj):
    """Print a deterministic representation of the given object.

    >>> print_unique_repr({8: {3,6,0}, 3: {5,4}})
    {3: {4, 5}, 8: {0, 3, 6}}

    """
    print(unique_repr(obj))

def splitarg_or_varargs(*args):
    """Construct a list of strings either from a single space-separated
string or from a variable number of string arguments.

    >>> splitarg_or_varargs('x y z')
    ['x', 'y', 'z']
    >>> splitarg_or_varargs('x', 'y', 'z')
    ['x', 'y', 'z']

    """
    if len(args) == 1:
        return args[0].split()
    else:
        return list(args)
