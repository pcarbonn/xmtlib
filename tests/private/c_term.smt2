(assert #x3F)
(declare-const p Bool)
(declare-const c Int)
(assert p)
(assert c)
;(assert (or p p))
(x-ground)
(x-debug solver groundings)
-------------------------
(declare-const p Bool)
(declare-const c Int)
(assert #x3F)
(assert p)
(assert c)
Groundings:
 - #x3F: SELECT "#x3F" AS G
 - p:
    TU: SELECT "p" AS G
    UF: SELECT "p" AS G
    G : SELECT "p" AS G
 - c: SELECT "c" AS G