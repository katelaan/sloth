(declare-const x sl.list.loc)
(declare-const a Int)
(assert (sl.sepcon (sl.list.dpred.unary (= sl.alpha sl.alpha) x) (= a 9001)))
(assert (not (sl.list.dpred.unary (not (= sl.alpha a)) x)))
