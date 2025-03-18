(set-option :backend none)
(assert (= 2 2 2))
(assert (not (= 2 2)))
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
Groundings:
 - 2: SELECT "2" AS G
 - (= 2 2 2):
    T: SELECT "true" AS G WHERE "2" = "2" AND "2" = "2"
    F: SELECT "false" AS G WHERE NOT "2" = "2" OR NOT "2" = "2"
    G : SELECT eq_("2", "2", "2") AS G
 - (= 2 2):
    T: SELECT "true" AS G WHERE "2" = "2"
    F: SELECT "false" AS G WHERE NOT "2" = "2"
    G : SELECT eq_("2", "2") AS G
 - (not (= 2 2)):
    T: SELECT "true" AS G WHERE NOT "2" = "2"
    F: SELECT "false" AS G WHERE "2" = "2"
    G : SELECT not_(eq_("2", "2")) AS G