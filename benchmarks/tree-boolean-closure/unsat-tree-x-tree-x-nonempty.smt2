;; depth = 3
(declare-const x sl.tree.loc)
(assert (sl.sepcon (sl.tree.neq x sl.tree.null)
                   (sl.sepcon (sl.tree x) (sl.tree x))))
