(set-option :backend none)
(assert (= 2 2 2))
(assert (not (= 2 2)))
(assert (= (= 2 2) (not (= 3 3))))
(assert (and (= 2 2) (not (= 3 3))))
(x-ground)
(x-debug solver groundings)
-------------------------





(push)
(assert (= 2 2 2))
(pop)
(assert true)
(push)
(assert (not (= 2 2)))
(pop)
(assert false)
(push)
(assert (= (= 2 2) (not (= 3 3))))
(pop)
(assert false)
(push)
(assert (and (= 2 2) (not (= 3 3))))
(pop)
(assert false)
Groundings:
 - 2: SELECT "2" AS G
 - (= 2 2 2):
    T: SELECT "true" AS G
    F: SELECT "true" AS G
    G : SELECT "true" AS G
 - (= 2 2):
    T: SELECT "true" AS G
    F: SELECT "true" AS G
    G : SELECT "true" AS G
 - (not (= 2 2)):
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT not_("true") AS G
 - 3: SELECT "3" AS G
 - (= 3 3):
    T: SELECT "true" AS G
    F: SELECT "true" AS G
    G : SELECT "true" AS G
 - (not (= 3 3)):
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT not_("true") AS G
 - (= (= 2 2) (not (= 3 3))):
    T: SELECT eq_("true", not_("true")) AS G
    F: SELECT eq_("true", not_("true")) AS G
    G : SELECT eq_("true", not_("true")) AS G
 - (and (= 2 2) (not (= 3 3))):
    T: SELECT "true" AS G
    UF: SELECT and_aggregate(G) as G from (SELECT "true" AS G UNION SELECT "false" AS G)
    G : SELECT and_("true", not_("true")) AS G