(set-option :backend none)
(assert (forall ((x Int)) true))
(assert (exists ((x Int)) true))
(declare-datatype Color ( ( red ) ( green ) ))
(assert (forall ((x Color)) true))
(assert (exists ((x Color)) true))
(declare-fun p (Color) Bool)
(assert (forall ((x Color)) (p x)))
(assert (exists ((x Color)) (p x)))
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (q x)))
(declare-fun r (Bool) Bool)
(assert (not (exists ((x Bool)) (r x))))
(assert (forall ((x Bool)) (=> (and (r x) (r x)) false)))

(x-ground)
(x-debug solver groundings)
(x-debug db-view negate_16)
-------------------------
(declare-datatype Color ((red ) (green )))
(declare-fun p (Color) Bool)
(declare-fun q (Int) Bool)
(declare-fun r (Bool) Bool)
(assert (p red))
(assert (p green))
(assert (or (p red) (p green)))
(assert (forall ((x Int)) (q x)))
(assert (and (not (r true)) (not (r false))))
(assert (not (r true)))
(assert (not (r false)))
Groundings:
 - true:
    T: SELECT "true" AS G
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (forall ((x Int)) true):
    TU: SELECT and_aggregate(G) as G from (SELECT "true" AS G)
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT and_aggregate(G) as G from (SELECT "true" AS G)
 - (exists ((x Int)) true):
    TU: SELECT or_aggregate(G) as G from (SELECT "true" AS G)
    UF: SELECT or_aggregate(G) as G from (SELECT "true" AS G)
    G : SELECT or_aggregate(G) as G from (SELECT "true" AS G)
 - (forall ((x Color)) true):
    TU: SELECT and_aggregate(G) as G from (SELECT "true" AS G)
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT and_aggregate(G) as G from (SELECT "true" AS G)
 - (exists ((x Color)) true):
    TU: SELECT or_aggregate(G) as G from (SELECT "true" AS G)
    UF: SELECT or_aggregate(G) as G from (SELECT "true" AS G)
    G : SELECT or_aggregate(G) as G from (SELECT "true" AS G)
 - x: SELECT Color_5.G AS x, Color_5.G AS G FROM Color AS Color_5
 - (p x):
    TU: SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5
    UF: SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5
    G : SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5
 - (forall ((x Color)) (p x)):
    TU: SELECT and_aggregate(G) as G from (SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5)
    UF: SELECT G as G from (SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5)
    G : SELECT and_aggregate(G) as G from (SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5)
 - (exists ((x Color)) (p x)):
    TU: SELECT or_aggregate(G) as G from (SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5)
    UF: SELECT or_aggregate(G) as G from (SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5)
    G : SELECT or_aggregate(G) as G from (SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5)
 - x: SELECT "x" AS x, "x" AS G
 - (q x):
    TU: SELECT "x" AS x, apply("q", "x") AS G
    UF: SELECT "x" AS x, apply("q", "x") AS G
    G : SELECT "x" AS x, apply("q", "x") AS G
 - (forall ((x Int)) (q x)):
    TU: SELECT "(forall ((x Int)) " || and_aggregate(G) || ")" as G from (SELECT "x" AS x, apply("q", "x") AS G)
    UF: SELECT "(forall ((x Int)) " || G || ")" as G from (SELECT "x" AS x, apply("q", "x") AS G)
    G : SELECT "(forall ((x Int)) " || and_aggregate(G) || ")" as G from (SELECT "x" AS x, apply("q", "x") AS G)
 - x: SELECT Bool_12.G AS x, Bool_12.G AS G FROM Bool AS Bool_12
 - (r x):
    TU: SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12
    UF: SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12
    G : SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12
 - (exists ((x Bool)) (r x)):
    TU: SELECT or_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12)
    UF: SELECT or_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12)
    G : SELECT or_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12)
 - (not (exists ((x Bool)) (r x))):
    TU: SELECT and_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)
    UF: SELECT and_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)
    G : SELECT and_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)
 - (not (r x)):
    TU: SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12
    UF: SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12
    G : SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12
 - false:
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G
    G : SELECT "false" AS G
 - (or (not (r x)) false):
    TU: SELECT negate_16.x AS x, negate_16.G AS G FROM negate_16
    UF: SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12
    G : SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12
 - (forall ((x Bool)) (or (not (r x)) false)):
    TU: SELECT and_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)
    UF: SELECT G as G from (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)
    G : SELECT and_aggregate(G) as G from (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)
CREATE VIEW negate_16 AS SELECT x, G FROM (SELECT Bool_12.G AS x, apply("not", apply("r", Bool_12.G)) AS G FROM Bool AS Bool_12)