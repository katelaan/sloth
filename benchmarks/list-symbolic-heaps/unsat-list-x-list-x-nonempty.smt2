(declare-const x sl.list.loc)
(assert (sl.sepcon (sl.list.neq x sl.list.null)
                   (sl.sepcon (sl.list x) (sl.list x))))
