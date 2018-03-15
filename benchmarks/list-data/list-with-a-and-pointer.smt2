(declare-const x sl.list.loc)
(declare-const xdata Int)
(declare-const a Int)
(assert (sl.sepcon (sl.list.pointsto x sl.list.null)
                   (sl.list.data x xdata)))
;; List whose values are not all not a
;; In other words: x contains a
(assert (not (sl.list.dpred.unary (not (= sl.alpha a)) x)))
(assert (= a 23))
