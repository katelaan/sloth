(declare-const t sl.tree.loc)
(declare-const d Int)
(assert (sl.sepcon (sl.tree t)
                   (= d 1)))
(assert (not (sl.tree.dpred.unary (not (= sl.alpha d)) t)))