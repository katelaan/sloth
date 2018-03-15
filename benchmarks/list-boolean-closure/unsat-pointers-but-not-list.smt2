(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(assert (sl.sepcon
         (sl.list.pointsto x y)
         (sl.list.pointsto y sl.list.null)))
(assert (not (sl.list x)))
