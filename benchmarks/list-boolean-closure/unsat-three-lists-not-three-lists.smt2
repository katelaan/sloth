(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const z sl.list.loc)
(assert (sl.sepcon (sl.sepcon (sl.list x)
                              (sl.list y))
                   (sl.list z)))
(assert (not (sl.sepcon (sl.sepcon (sl.list x)
                              (sl.list y))
                   (sl.list z))))
