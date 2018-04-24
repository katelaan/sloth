;; Tool paper, Sec. 2, p. 4, third example
;; (list(x, y) * list(y)) /\ (not list(x))
(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(assert (and
         (sl.sepcon (sl.list.seg x y) (sl.list y))
         (not (sl.list x))))
