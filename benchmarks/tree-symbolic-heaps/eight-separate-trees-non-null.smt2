(declare-const a sl.tree.loc)
(declare-const b sl.tree.loc)
(declare-const c sl.tree.loc)
(declare-const d sl.tree.loc)
(declare-const e sl.tree.loc)
(declare-const f sl.tree.loc)
(declare-const g sl.tree.loc)
(declare-const h sl.tree.loc)
(assert (sl.sepcon (sl.sepcon
                   (sl.sepcon
                    (sl.sepcon (sl.tree a) (sl.tree b))
                    (sl.sepcon (sl.tree c) (sl.tree d)))
                   (sl.sepcon
                    (sl.sepcon (sl.tree e) (sl.tree f))
                    (sl.sepcon (sl.tree g) (sl.tree h))))
                  (sl.sepcon
                   (sl.sepcon
                    (sl.sepcon (sl.tree.neq a sl.tree.null)
                               (sl.tree.neq b sl.tree.null))
                    (sl.sepcon (sl.tree.neq c sl.tree.null)
                               (sl.tree.neq d sl.tree.null)))
                   (sl.sepcon
                    (sl.sepcon (sl.tree.neq e sl.tree.null)
                               (sl.tree.neq f sl.tree.null))
                    (sl.sepcon (sl.tree.neq g sl.tree.null)
                               (sl.tree.neq h sl.tree.null))))))
