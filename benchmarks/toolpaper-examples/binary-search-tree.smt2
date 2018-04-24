;; Tool paper, Sec. 2, p. 4, second example
;; tree(t,{(l, beta < alpha), (r, beta > alpha)})
(declare-const t sl.tree.loc)
(assert (sl.tree.dpred.left (> sl.alpha sl.beta) t))
(assert (sl.tree.dpred.right (< sl.alpha sl.beta) t))
