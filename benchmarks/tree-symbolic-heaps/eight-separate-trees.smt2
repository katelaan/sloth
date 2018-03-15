(declare-const a sl.tree.loc)
(declare-const b sl.tree.loc)
(declare-const c sl.tree.loc)
(declare-const d sl.tree.loc)
(declare-const e sl.tree.loc)
(declare-const f sl.tree.loc)
(declare-const g sl.tree.loc)
(declare-const h sl.tree.loc)
(assert (sl.sepcon
         (sl.sepcon
          (sl.sepcon (sl.tree a) (sl.tree b))
          (sl.sepcon (sl.tree c) (sl.tree d)))
         (sl.sepcon
          (sl.sepcon (sl.tree e) (sl.tree f))
          (sl.sepcon (sl.tree g) (sl.tree h)))))
