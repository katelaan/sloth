;; Tool paper, Sec. 2, p. 3, first example
;; (x ->_n y) * (x ->_d d) * (d > 0)
(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const d Int)
(assert (sl.sepcon (sl.sepcon
                    (sl.list.next x y)
                    (sl.list.data x d)
                    )
                   (> d 0)))
