(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const b sl.list.loc)
(declare-const d sl.list.loc)
(declare-const xdata Int)
(declare-const ydata Int)
(declare-const bdata Int)
(declare-const ddata Int)
(declare-const A Int)
(assert (sl.sepcon (= A 9001)
                   (sl.sepcon (sl.list.dpred.unary (= sl.alpha sl.alpha) x)
                              (sl.list.dpred.unary (not (= sl.alpha A)) y))))
(assert (not (sl.sepcon (sl.list.dpred.unary (not (= sl.alpha A)) x)
                        (sl.list.dpred.unary (= sl.alpha sl.alpha) y))))
