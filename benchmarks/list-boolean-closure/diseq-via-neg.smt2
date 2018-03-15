(declare-const a sl.list.loc)
(declare-const b sl.list.loc)
(declare-const c sl.list.loc)
;; Assert a -> c
(assert (sl.list.pointsto a c))
;; Asserting not (a -> b) should enforce a model where b != c
(assert (not (sl.list.pointsto a b)))
