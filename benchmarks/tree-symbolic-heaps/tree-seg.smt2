(declare-const a sl.tree.loc)
(declare-const b sl.tree.loc)
(declare-const c sl.tree.loc)
(declare-const d sl.tree.loc)
(assert (sl.sepcon
         (sl.tree.neq a b)
         (sl.sepcon (sl.tree.seg a b) (sl.tree.pointsto b c d))))
