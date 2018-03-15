(declare-const a sl.list.loc)
(declare-const b sl.list.loc)
(declare-const adata Int)
(declare-const bdata Int)
(assert (sl.list.dpred.unary (= sl.alpha 0) a))
;; Assert a few pointers as a classical conjunction to force length
(assert (sl.sepcon
         (sl.sepcon (sl.list.pointsto a b) (sl.list.pointsto b sl.list.null))
         (sl.sepcon (sl.list.data a adata) (sl.list.data b bdata))))
