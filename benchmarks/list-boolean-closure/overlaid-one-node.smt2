(declare-const a sl.list.loc)
(declare-const d Int)
(assert (and (sl.list a)
             (sl.sepcon (sl.list.pointsto a sl.list.null)
                        (sl.list.data a d))))
