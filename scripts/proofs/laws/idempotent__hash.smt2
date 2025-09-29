(declare-sort Val 0)
(declare-fun H (Val) Val)
(assert (forall ((x Val)) (= (H (H x)) (H x))))
(check-sat)
