;; Tool paper, Sec. 2, p. 3, third example
;; tree(t, <u,v>) * (u ->_{l,r,d} (null,null,d)) * (v ->_{l,r,d} (null,null,e)) * (d > e)
(declare-const t sl.tree.loc)
(declare-const u sl.tree.loc)
(declare-const v sl.tree.loc)
(declare-const d Int)
(declare-const e Int)
(assert (sl.sepcon
         (sl.sepcon (> d e) (sl.tree.seg2 t u v))
         (sl.sepcon (sl.tree.dpointsto u sl.tree.null sl.tree.null d)
                    (sl.tree.dpointsto v sl.tree.null sl.tree.null e))))
