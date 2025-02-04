(assert #x3F)
(declare-const p Bool)
(declare-const c Int)
(assert p)
(assert c)
(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun q (Color) Bool)
(assert (q red))
(assert (or (q red) (q green)))
;(assert (or p p))
(x-ground)
(x-debug solver groundings)
-------------------------

(declare-const p Bool)
(declare-const c Int)


(declare-datatype Color ((red ) (green )))
(declare-fun q (Color) Bool)


(assert #x3F)
(assert p)
(assert c)
(assert (q red))
(assert (or (q red) (q green)))
Groundings:
 - #x3F: SELECT "#x3F" AS G
 - p: SELECT "p" AS G
 - c: SELECT "c" AS G
 - (q red): SELECT apply("q", "red") AS G
 - (or (q red) (q green)): SELECT apply("or", apply("q", "red"), apply("q", "green")) AS G