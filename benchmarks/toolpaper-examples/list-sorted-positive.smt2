;; Tool paper, Sec. 2, p. 4, first example
;; list(x, {alpha > 0, (n, alpha < beta)})
(declare-const x sl.list.loc)
(assert (and (sl.list.dpred.unary (> sl.alpha 0) x)
             (sl.list.dpred.next (< sl.alpha sl.beta) x)))
