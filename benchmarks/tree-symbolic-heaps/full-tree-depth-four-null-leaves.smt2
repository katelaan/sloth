(declare-const x sl.tree.loc)
(declare-const l sl.tree.loc)
(declare-const r sl.tree.loc)
(declare-const ll sl.tree.loc)
(declare-const lr sl.tree.loc)
(declare-const rl sl.tree.loc)
(declare-const rr sl.tree.loc)
(declare-const lll sl.tree.loc)
(declare-const llr sl.tree.loc)
(declare-const lrl sl.tree.loc)
(declare-const lrr sl.tree.loc)
(declare-const rll sl.tree.loc)
(declare-const rlr sl.tree.loc)
(declare-const rrl sl.tree.loc)
(declare-const rrr sl.tree.loc)
(assert (sl.sepcon
         (sl.sepcon
          (sl.sepcon (sl.tree.pointsto x l r)
                     (sl.sepcon (sl.tree.pointsto l ll lr)
                                (sl.tree.pointsto r rl rr)))
          (sl.sepcon (sl.sepcon (sl.tree.pointsto ll lll llr)
                                (sl.tree.pointsto lr lrl lrr))
                     (sl.sepcon (sl.tree.pointsto rl rll rlr)
                                (sl.tree.pointsto rr rrl rrr))))
         (sl.sepcon
          (sl.sepcon
           (sl.sepcon (sl.tree.eq lll sl.tree.null)
                      (sl.tree.eq llr sl.tree.null))
           (sl.sepcon (sl.tree.eq lrl sl.tree.null)
                      (sl.tree.eq lrr sl.tree.null)))
          (sl.sepcon
           (sl.sepcon (sl.tree.eq rll sl.tree.null)
                      (sl.tree.eq rlr sl.tree.null))
           (sl.sepcon (sl.tree.eq rrl sl.tree.null)
                      (sl.tree.eq rrr sl.tree.null))))))
