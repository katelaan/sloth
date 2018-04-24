;; Tool paper, Sec. 2, p. 3, second example
;; list(x, y) * (y ->_{n,d} (z, d)) * list(z)
(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const z sl.list.loc)
(declare-const d Int)
(assert (sl.sepcon
         (sl.sepcon (sl.list.seg x y) (sl.list.next y z))
         (sl.sepcon (sl.list.data y d) (sl.list z))))
