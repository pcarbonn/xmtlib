(assert (forall ((x Int)) true))
(assert (exists ((x Int)) true))
(declare-datatype Color ( ( red ) ( green ) ))
(assert (forall ((x Color)) true))
(assert (exists ((x Color)) true))
(x-ground)
(x-debug solver groundings)
(x-debug db Agg_4_TU)
-------------------------


(declare-datatype Color ((red ) (green )))


(push)
(assert (forall ((x Int)) true))
(pop)
(assert (forall ((x Int)) (and true)))
(push)
(assert (exists ((x Int)) true))
(pop)
(assert (exists ((x Int)) (or true)))
(push)
(assert (forall ((x Color)) true))
(pop)
(assert (and true))
(push)
(assert (exists ((x Color)) true))
(pop)
(assert (or true))
Groundings:
 - true:
    TU: SELECT "true" AS G
    UF: SELECT "true" AS G
    G : SELECT "true" AS G
 - (forall ((x Int)) true):
    TU: SELECT Agg_1_TU.G AS G FROM Agg_1_TU
    UF: SELECT Agg_1_UF.G AS G FROM Agg_1_UF
    G : SELECT Agg_1_G.G AS G FROM Agg_1_G
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
 TABLE: Agg_4_TU
┌─────────────┐
│ G           │
├─────────────┤
│ "(or true)" │
└─────────────┘