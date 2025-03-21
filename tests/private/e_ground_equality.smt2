(set-option :backend none)
(assert (= 2 2 2))
(assert (not (= 2 2)))
(assert (= (= 2 2) (not (= 3 3))))
(x-ground)
(x-debug solver groundings)
-------------------------




(push)
(assert (= 2 2 2))
(pop)
(push)
(assert (not (= 2 2)))
(pop)
(assert false)
(push)
(assert (= (= 2 2) (not (= 3 3))))
(pop)
(assert false)
Groundings:
 - 2: SELECT "2" AS G
 - (= 2 2 2):
    T: SELECT "true" AS G WHERE TRUE
    F: SELECT "false" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (= 2 2):
    T: SELECT "true" AS G WHERE TRUE
    F: SELECT "false" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (not (= 2 2)):
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G WHERE TRUE
    G : SELECT not_("true") AS G
 - 3: SELECT "3" AS G
 - (= 3 3):
    T: SELECT "true" AS G WHERE TRUE
    F: SELECT "false" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (not (= 3 3)):
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G WHERE TRUE
    G : SELECT not_("true") AS G
 - (= (= 2 2) (not (= 3 3))):
    T: SELECT "true" AS G WHERE TRUE = FALSE
    F: SELECT "false" AS G WHERE NOT (TRUE = FALSE)
    G : SELECT eq_({terms}) AS G