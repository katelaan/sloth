(declare-const a sl.list.loc)
(declare-const b sl.list.loc)
(declare-const c sl.list.loc)
;; Assert a -> c
;; Declare b != null to force z3 to instantiate b
(assert (sl.sepcon (sl.list.pointsto a c) (sl.list.neq b sl.list.null)))
;; Asserting not (a -> b) should enforce a model where b != c
(assert (not (sl.list.pointsto a b)))
