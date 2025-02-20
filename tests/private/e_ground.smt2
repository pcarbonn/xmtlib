(set-option :backend none)
(assert false)
(assert (and true true))
(assert (or false false))
(x-ground)
(x-debug solver groundings)
-------------------------




(push)
(assert false)
(pop)
(assert false)
(push)
(assert (and true true))
(pop)
(assert false)
(push)
(assert (or false false))
(pop)
(assert false)
Groundings:
 - false:
    T: SELECT "false" AS G WHERE FALSE
    F: SELECT "false" AS G
    G : SELECT "false" AS G
 - true:
    T: SELECT "true" AS G
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (and true true):
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT "true" AS G
 - (or false false):
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT "false" AS G