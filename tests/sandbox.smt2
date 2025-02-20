(set-option :backend none)
(assert true)
(x-ground)
(x-debug solver groundings)
-------------------------


(push)
(assert true)
(pop)
Groundings:
 - true:
    T: SELECT "true" AS G
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT "true" AS G