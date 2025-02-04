(assert #x3F)
(declare-const p Bool)
(declare-const c Int)
(assert p)
(assert c)
(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun q (Color) Bool)
(assert (q red))
(assert (or (q red) (q green)))
(assert (or (q red) (q red)))
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
(assert (or (q red) (q red)))
Groundings:
 - #x3F: SELECT "#x3F" AS G
 - p:
    TU: SELECT "p" AS G
    UF: SELECT "p" AS G
    G : SELECT "p" AS G
 - c: SELECT "c" AS G
 - red: SELECT "red" AS G
 - (q red):
    TU: SELECT apply("q", "red") AS G
    UF: SELECT apply("q", "red") AS G
    G : SELECT apply("q", "red") AS G
 - green: SELECT "green" AS G
 - (q green):
    TU: SELECT apply("q", "green") AS G
    UF: SELECT apply("q", "green") AS G
    G : SELECT apply("q", "green") AS G
 - (or (q red) (q green)):
    TU: SELECT apply("or", apply("q", "red"), apply("q", "green")) AS G
    UF: SELECT apply("or", apply("q", "red"), apply("q", "green")) AS G
    G : SELECT apply("or", apply("q", "red"), apply("q", "green")) AS G
 - (or (q red) (q red)):
    TU: SELECT apply("or", apply("q", "red"), apply("q", "red")) AS G
    UF: SELECT apply("or", apply("q", "red"), apply("q", "red")) AS G
    G : SELECT apply("or", apply("q", "red"), apply("q", "red")) AS G