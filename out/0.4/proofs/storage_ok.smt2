; SMT encoding for parallel write conflicts
(declare-const uri_0_0 String)
(declare-const uri_0_1 String)
(assert (= uri_0_0 "res://kv/bucket"))
(assert (= uri_0_1 "res://kv/other"))
(declare-const conflict_0_0_1 Bool)
(assert (= conflict_0_0_1 (= uri_0_0 uri_0_1)))
(assert (not (or conflict_0_0_1)))
(check-sat)
