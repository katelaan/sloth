(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const d Int)
(declare-const e Int)
(assert (sl.sepcon
         (sl.list.dpointsto x y d)
         (sl.list.dpointsto y sl.list.null e)))
(assert (not (sl.list x)))
