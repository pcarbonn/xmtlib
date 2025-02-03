(assert #x3F)
(declare-const p Bool)
(declare-const c Int)
;(assert p)
;(assert c)
;(assert (or p p))
(x-ground)
(x-debug solver groundings)
-------------------------

(declare-const p Bool)
(declare-const c Int)
(assert #x3F)
Groundings:
 - #x3F: SELECT "#x3F" AS G