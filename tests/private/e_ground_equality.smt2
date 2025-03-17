(set-option :backend none)
(assert (= 2 2))
(x-ground)
(x-debug solver groundings)
-------------------------


(push)
(assert (= 2 2))
(pop)
(assert (= 2 2))
Groundings:
 - 2: SELECT "2" AS G
 - (= 2 2):
    T: SELECT apply("=", "2", "2") AS G
    F: SELECT apply("=", "2", "2") AS G
    G : SELECT apply("=", "2", "2") AS G