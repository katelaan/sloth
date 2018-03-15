(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const A Int)
(assert (sl.sepcon (sl.list.dpred.unary (= sl.alpha sl.alpha) x)
                   (sl.list.dpred.unary (= sl.alpha sl.alpha) y)))
; Should force A to occur in the list that starts in X. But currently doesn't...
(assert (not (sl.sepcon (sl.list.dpred.unary (not (= sl.alpha A)) x)
                        (sl.list.dpred.unary (= sl.alpha sl.alpha) y))))
(assert (= A 9001))
