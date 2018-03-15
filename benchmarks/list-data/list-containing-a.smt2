(declare-const x sl.list.loc)
(declare-const a Int)
;; x is a list with allocated data field
;; Note: We have to assert a vacuous data constraint
;; Otherwise the solver will default to a spatial core logic and not allocate data
(assert (sl.list.dpred.unary (= sl.alpha sl.alpha) x))
;; ...whose values are not all not a
;; In other words: x contains a
(assert (not (sl.list.dpred.unary (not (= sl.alpha a)) x)))
(assert (= a 9001))
