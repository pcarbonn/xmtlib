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
(assert (exists ((x Bool)) (r x)))

(x-ground)
(x-debug solver groundings)
(x-debug db-view Agg_5_UF)
-------------------------


(declare-datatype Color ((red ) (green )))


(declare-fun p (Color) Bool)


(declare-fun q (Int) Bool)

(declare-fun r (Bool) Bool)

(push)
(assert (forall ((x Int)) true))
(pop)
(assert (forall ((x Int)) true))
(push)
(assert (exists ((x Int)) true))
(pop)
(assert (exists ((x Int)) true))
(push)
(assert (forall ((x Color)) true))
(pop)
(assert true)
(push)
(assert (exists ((x Color)) true))
(pop)
(assert true)
(push)
(assert (forall ((x Color)) (p x)))
(pop)
(assert (and (p red) (p green)))
(push)
(assert (exists ((x Color)) (p x)))
(pop)
(assert (or (p red) (p green)))
(push)
(assert (forall ((x Int)) (q x)))
(pop)
(assert (forall ((x Int)) (q x)))
(push)
(assert (exists ((x Bool)) (r x)))
(pop)
(assert (or (r true) (r false)))
Groundings:
 - true:
    TU: SELECT "true" AS G
    UF: SELECT "true" AS G
    G : SELECT "true" AS G
 - (forall ((x Int)) true):
    TU: SELECT Agg_0_TU.G AS G FROM Agg_0_TU
    UF: SELECT Agg_0_UF.G AS G FROM Agg_0_UF
    G : SELECT Agg_0_G.G AS G FROM Agg_0_G
 - (exists ((x Int)) true):
    TU: SELECT Agg_2_TU.G AS G FROM Agg_2_TU
    UF: SELECT Agg_2_UF.G AS G FROM Agg_2_UF
    G : SELECT Agg_2_G.G AS G FROM Agg_2_G
 - (forall () true):
    TU: SELECT Agg_3_TU.G AS G FROM Agg_3_TU
    UF: SELECT Agg_3_UF.G AS G FROM Agg_3_UF
    G : SELECT Agg_3_G.G AS G FROM Agg_3_G
 - (exists () true):
    TU: SELECT Agg_4_TU.G AS G FROM Agg_4_TU
    UF: SELECT Agg_4_UF.G AS G FROM Agg_4_UF
    G : SELECT Agg_4_G.G AS G FROM Agg_4_G
 - x: SELECT Color_5.G AS x, Color_5.G AS G FROM Color AS Color_5
 - (p x):
    TU: SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5
    UF: SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5
    G : SELECT Color_5.G AS x, apply("p", Color_5.G) AS G FROM Color AS Color_5
 - (forall () (p x)):
    TU: SELECT Agg_5_TU.G AS G FROM Agg_5_TU
    UF: SELECT Agg_5_UF.G AS G FROM Agg_5_UF
    G : SELECT Agg_5_G.G AS G FROM Agg_5_G
 - (exists () (p x)):
    TU: SELECT Agg_8_TU.G AS G FROM Agg_8_TU
    UF: SELECT Agg_8_UF.G AS G FROM Agg_8_UF
    G : SELECT Agg_8_G.G AS G FROM Agg_8_G
 - x: SELECT "x" AS G
 - (q x):
    TU: SELECT apply("q", "x") AS G
    UF: SELECT apply("q", "x") AS G
    G : SELECT apply("q", "x") AS G
 - (forall ((x Int)) (q x)):
    TU: SELECT Agg_9_TU.G AS G FROM Agg_9_TU
    UF: SELECT Agg_9_UF.G AS G FROM Agg_9_UF
    G : SELECT Agg_9_G.G AS G FROM Agg_9_G
 - x: SELECT Bool_12.G AS x, Bool_12.G AS G FROM Bool AS Bool_12
 - (r x):
    TU: SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12
    UF: SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12
    G : SELECT Bool_12.G AS x, apply("r", Bool_12.G) AS G FROM Bool AS Bool_12
 - (exists () (r x)):
    TU: SELECT Agg_12_TU.G AS G FROM Agg_12_TU
    UF: SELECT Agg_12_UF.G AS G FROM Agg_12_UF
    G : SELECT Agg_12_G.G AS G FROM Agg_12_G
CREATE VIEW Agg_5_UF AS SELECT and_aggregate(apply("p", Color_5.G)) AS G FROM Color AS Color_5