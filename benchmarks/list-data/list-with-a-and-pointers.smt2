(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const xdata Int)
(declare-const ydata Int)
(declare-const a Int)
(assert (sl.sepcon (sl.sepcon (sl.list.pointsto x y)
                              (sl.list.pointsto y sl.list.null))
                   (sl.sepcon (sl.list.data x xdata)
                              (sl.list.data y ydata))))
;; List whose values are not all not a
;; In other words: x contains a
(assert (not (sl.list.dpred.unary (not (= sl.alpha a)) x)))
(assert (= a 23))
