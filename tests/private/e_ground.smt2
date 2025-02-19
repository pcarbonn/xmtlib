(set-option :backend none)
(assert false)
(assert (or false false))
(x-ground)
(x-debug solver groundings)
-------------------------



(push)
(assert false)
(pop)
(assert false)
(push)
(assert (or false false))
(pop)
(assert (or false false))
Groundings:
 - false:
    TU: SELECT "false" AS G
    UF: SELECT "false" AS G
    G : SELECT "false" AS G
 - (or false false):
    TU: SELECT apply("or", "false", "false") AS G
    UF: SELECT apply("or", "false", "false") AS G
    G : SELECT apply("or", "false", "false") AS G