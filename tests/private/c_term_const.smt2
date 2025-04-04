(set-option :backend none)
(assert true)
(declare-const p Bool)
(declare-const c Int)
(assert p)
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



(assert p)
(assert (q red))
(assert (or (q red) (q green)))
(assert (or (q red) (q red)))
Groundings:
 - true:
    T: SELECT "true" AS G
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT "true" AS G
 - p:
    TU: SELECT "p" AS G
    UF: SELECT "p" AS G
    G : SELECT "p" AS G
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
    TU: SELECT or_aggregate(G) as G from (SELECT apply("q", "red") AS G UNION SELECT apply("q", "green") AS G)
    UF: SELECT apply("or", apply("q", "red"), apply("q", "green")) AS G
    G : SELECT apply("or", apply("q", "red"), apply("q", "green")) AS G
 - (or (q red) (q red)):
    TU: SELECT or_aggregate(G) as G from (SELECT apply("q", "red") AS G UNION SELECT apply("q", "red") AS G)
    UF: SELECT apply("or", apply("q", "red"), apply("q", "red")) AS G
    G : SELECT apply("or", apply("q", "red"), apply("q", "red")) AS G