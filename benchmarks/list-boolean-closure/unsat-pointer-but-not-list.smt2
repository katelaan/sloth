(declare-const x sl.list.loc)
(declare-const xn sl.list.loc)
(assert (sl.list.pointsto x sl.list.null))
(assert (not (sl.list x)))
;; Have to assert separately, is not enforced by encoding
(assert (= xn sl.list.null))
