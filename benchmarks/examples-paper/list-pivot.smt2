(declare-const x sl.list.loc) ;; head of first list
(declare-const m sl.list.loc) ;; pivot element
(declare-const y sl.list.loc) ;; head of second list
(declare-const a sl.list.loc)
(declare-const b sl.list.loc)
(declare-const d sl.list.loc)
(declare-const e sl.list.loc)
(declare-const f sl.list.loc)
(declare-const g sl.list.loc)
(declare-const xdata Int)
(declare-const mdata Int)
(declare-const ydata Int)
(declare-const adata Int)
(declare-const bdata Int)
(declare-const ddata Int)
(declare-const edata Int)
(declare-const fdata Int)
(declare-const M Int) ;; the pivot data
(assert (sl.sepcon
         (sl.sepcon
          (sl.list.dpred.unary1 (< sl.alpha M) x m)
          (sl.list.dpred.unary (> sl.alpha M) y))
         (sl.sepcon
          (sl.list.next m y)
          (sl.list.data m M))))
;; Assert a few pointers as a classical conjunction to force length
(assert (sl.sepcon
         (sl.sepcon
          (sl.sepcon
           (sl.sepcon (sl.list.pointsto x a) (sl.list.pointsto a b))
           (sl.sepcon (sl.list.pointsto b m) (sl.list.pointsto m y)))
          (sl.sepcon
           (sl.sepcon (sl.list.pointsto y d) (sl.list.pointsto d e))
           (sl.sepcon (sl.list.pointsto e f) (sl.list.pointsto f g))))
         (sl.sepcon
          (sl.sepcon
           (sl.sepcon (sl.list.data x xdata) (sl.list.data a adata))
           (sl.sepcon (sl.list.data b bdata) (sl.list.data m mdata)))
          (sl.sepcon
           (sl.sepcon (sl.list.data y ydata) (sl.list.data d ddata))
           (sl.sepcon (sl.list.data e edata) (sl.list.data f fdata))))))
