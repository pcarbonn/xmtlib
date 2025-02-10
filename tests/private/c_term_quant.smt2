(assert (forall ((x Int)) true))
(assert (exists ((x Int)) true))
(x-ground)
(x-debug solver groundings)
-------------------------


(push)
(assert (forall ((x Int)) true))
(pop)
(assert (forall ((x Int)) (and true)))
(push)
(assert (exists ((x Int)) true))
(pop)
(assert (exists ((x Int)) (or true)))
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