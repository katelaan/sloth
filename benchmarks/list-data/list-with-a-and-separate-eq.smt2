(declare-const x sl.list.loc)
(declare-const y sl.list.loc)
(declare-const A Int)
(assert (sl.sepcon (sl.list.dpred.unary (= sl.alpha sl.alpha) x)
                   (sl.list.eq y sl.list.null)))
; Force A to occur in the list that starts in X
(assert (not (sl.sepcon (sl.list.dpred.unary (not (= sl.alpha A)) x)
                        (sl.list.eq y sl.list.null))))
(assert (= A 9001))
