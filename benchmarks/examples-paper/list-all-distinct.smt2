(declare-const a sl.list.loc)
(declare-const b sl.list.loc)
(declare-const c sl.list.loc)
(declare-const d sl.list.loc)
(declare-const e sl.list.loc)
(declare-const adata Int)
(declare-const bdata Int)
(declare-const cdata Int)
(declare-const ddata Int)
(assert (sl.list.dpred.next (not (= sl.alpha sl.beta)) a))
;; Assert a few pointers as a classical conjunction to force length
(assert (sl.sepcon
         (sl.sepcon
          (sl.sepcon (sl.list.pointsto a b) (sl.list.pointsto b c))
          (sl.sepcon (sl.list.pointsto c d) (sl.list.pointsto d e)))
         (sl.sepcon
          (sl.sepcon (sl.list.data a adata) (sl.list.data b bdata))
          (sl.sepcon (sl.list.data c cdata) (sl.list.data d ddata)))))
