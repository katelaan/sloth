(declare-const a sl.list.loc)
(assert (and (sl.list a)
             (sl.list.pointsto a sl.list.null)))
