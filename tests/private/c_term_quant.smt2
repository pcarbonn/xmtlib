(assert (forall ((x Int)) true))
(x-ground)
(x-debug solver groundings)
-------------------------

(push)
(assert (forall ((x Int)) true))
(pop)
(assert (and true))
Groundings:
 - true:
    TU: SELECT "true" AS G
    UF: SELECT "true" AS G
    G : SELECT "true" AS G
 - (forall ((x Int)) true):
    TU: SELECT Agg_1_TU.G AS G FROM Agg_1_TU
    UF: SELECT Agg_1_UF.G AS G FROM Agg_1_UF
    G : SELECT Agg_1_G.G AS G FROM Agg_1_G