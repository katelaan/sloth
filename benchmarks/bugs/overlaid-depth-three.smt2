;; This example currently triggers very strange behavior with z3
;; Looks like a hash conflict inside z3's own DAG representation,
;; leading to a completely different expression being returned from
;; the unfolding than is actually generated.
;; Have to investigate this further at some point...
(declare-const x sl.tree.loc)
(declare-const l sl.tree.loc)
(declare-const r sl.tree.loc)
(declare-const ll sl.tree.loc)
(declare-const lr sl.tree.loc)
(declare-const rl sl.tree.loc)
(declare-const rr sl.tree.loc)
(assert (sl.sepcon
         (sl.sepcon (sl.tree.pointsto x l r)
                    (sl.sepcon (sl.tree.pointsto l ll lr)
                               (sl.tree.pointsto r rl rr)))
         (sl.sepcon
          (sl.sepcon (sl.tree.neq ll sl.tree.null)
                     (sl.tree.neq lr sl.tree.null))
          (sl.sepcon (sl.tree.neq rl sl.tree.null)
                     (sl.tree.neq rr sl.tree.null)))))
(assert (sl.tree x))
