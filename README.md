# sloth
sloth is a solver for SL*, a Separation Logic modulo THeories introduced in the IJCAR'18 paper "A Separation Logic with Data: Small Models and Automation." sloth solves SL* formulas by encoding them into SMT assertions that are discharged by the SMT solver Z3.

## Install instructions

sloth requires Python >= 3.5. Sample install instructions for Debian-based systems:

```
sudo apt install python3-dev python3-ven
python3 -m venv venv
source venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
deactivate
```

## Running sloth

sloth has a command-line interface that can be invoked via the `sloth.sh` script in the root folder of the repository. For example, try

```
$ ./sloth.sh benchmarks/list-data/sorted-list.smt2`
```

## Input format

The sloth command-line interface processes a custom extension
of the SMT-LIB format. This custom extension
supports all features of SL* on top of SMT-LIB.

For example, the following input asserts that the heap consists of a list segment from `x` to `y`; a list node `y` pointing to `z` and to a positive data value `d`; and a list from `z` to `null`.

```smt
(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const z sl.list.loc)
(declare-const d Int)
(assert (sl.sepcon (> d 0)
         (sl.sepcon
          (sl.sepcon (sl.list.seg x y) (sl.list.next y z))
          (sl.sepcon (sl.list.data y d) (sl.list z)))))
```

Many more examples can be found in the [benchmarks](https://github.com/katelaan/sloth/tree/master/benchmarks) folder of the repository.

## Sloth API

sloth also comes with a python API that extends Z3's Python API with SL* features. For example:

```python
from z3 import And, Not, Ints
from sloth import *

x, y, z = sl.list.locs('x y z')
d, e = Ints('d e')

# Construct SL* expressions with the same syntax used in the SMT-LIB extension
# They are ordinary z3 expression references and can thus be freely combined with z3 expressions
expr1 = sl.sepcon(sl.list.seg(x, y), sl.list.neq(x,y))
expr2 = Not(sl.sepcon(sl.list.next(x, z), sl.list.next(z,y), sl.list.data(x,d), sl.list.data(y,e)))
expr = And(expr1, expr2)

# Check satisfiability
is_sat(expr)
Out: True
# Get model
model(expr)
Out: Model [
       Struct sl.list [
         locs = Integers(6:[z, x], 7:[y])
         null = 2
         next = 6->7
         data = 6->9
       ]
     ]
```
