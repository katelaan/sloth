;; bound = 7
;; This is only satisfiable for depth >= 8
;; The above depth bound should just lead to an UNSAT result
(declare-const a sl.list.loc)
(declare-const b sl.list.loc)
(declare-const c sl.list.loc)
(declare-const d sl.list.loc)
(declare-const e sl.list.loc)
(declare-const f sl.list.loc)
(declare-const g sl.list.loc)
(declare-const h sl.list.loc)
(assert (sl.sepcon
         (sl.sepcon (sl.sepcon (sl.list.pointsto a b)
                               (sl.list.pointsto b c))
                    (sl.sepcon (sl.list.pointsto c d)
                               (sl.list.pointsto d e)))
         (sl.sepcon (sl.sepcon (sl.list.pointsto e f)
                               (sl.list.pointsto f g))
                    (sl.sepcon (sl.list.pointsto g h)
                               (sl.list.pointsto h sl.list.null)))))
(assert (sl.list a))
