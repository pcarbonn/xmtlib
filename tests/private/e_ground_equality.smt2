(set-option :backend none)
(assert (= 2 2 2))
(x-ground)
(x-debug solver groundings)
-------------------------


(push)
(assert (= 2 2 2))
(pop)
(assert true)
Groundings:
 - 2: SELECT "2" AS G
 - (= 2 2 2):
    T: SELECT eq_("2", "2", "2") AS G
    F: SELECT eq_("2", "2", "2") AS G
    G : SELECT eq_("2", "2", "2") AS G