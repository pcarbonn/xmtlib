(set-option :backend none)
(declare-datatype Node ( ( |1| ) ( |2| ) ( |3| )))
(declare-fun Edge (Node Node) Bool)
(declare-fun phi (Node Node Node) Bool)
(x-interpret-pred Edge
    (|1| |2|)
    (|2| |3|)
    (|1| |3|)
)
(assert (forall ((x Node) (y Node) (z Node))
            (=> (and (Edge x y) (Edge y z) (Edge x z))
                     (phi x y z)
            )))
(assert (forall ((x Node)) (Edge x x)))
(assert (exists ((x Node) (y Node)) (Edge x y)))
(x-ground)
(x-debug db-view Agg_14_UF)
(x-debug solver groundings)
(check-sat)
-------------------------

(declare-datatype Node ((|1| ) (|2| ) (|3| )))
(declare-fun Edge (Node Node) Bool)
(declare-fun phi (Node Node Node) Bool)
(x-interpret-pred Edge (|1| |2|) (|2| |3|) (|1| |3|))



(push)
(assert (forall ((x Node) (y Node) (z Node)) (=> (and (Edge x y) (Edge y z) (Edge x z)) (phi x y z))))
(pop)
(assert (phi |1| |2| |3|))
(push)
(assert (forall ((x Node)) (Edge x x)))
(pop)
(assert false)
(push)
(assert (exists ((x Node) (y Node)) (Edge x y)))
(pop)
(assert true)
CREATE VIEW Agg_14_UF AS SELECT or_aggregate(G) as G from (SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G.G AS G FROM Edge_G AS Edge_G) HAVING or_aggregate(G) <> true
Groundings:
 - x: SELECT Node.G AS x, Node.G AS G FROM Node
 - y: SELECT Node_1.G AS y, Node_1.G AS G FROM Node AS Node_1
 - (Edge x y):
    T: SELECT Edge_TU.a_0 AS x, Edge_TU.a_1 AS y, Edge_TU.G AS G FROM Edge_TU AS Edge_TU
    F: SELECT Edge_UF.a_0 AS x, Edge_UF.a_1 AS y, Edge_UF.G AS G FROM Edge_UF AS Edge_UF
    G : SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G.G AS G FROM Edge_G AS Edge_G
 - (not (Edge x y)):
    T: SELECT Edge_UF.a_0 AS x, Edge_UF.a_1 AS y, "true" AS G FROM Edge_UF AS Edge_UF
    F: SELECT Edge_TU.a_0 AS x, Edge_TU.a_1 AS y, "false" AS G FROM Edge_TU AS Edge_TU
    G : SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, not_(Edge_G.G) AS G FROM Edge_G AS Edge_G
 - z: SELECT Node_4.G AS z, Node_4.G AS G FROM Node AS Node_4
 - (Edge y z):
    T: SELECT Edge_TU_4.a_0 AS y, Edge_TU_4.a_1 AS z, Edge_TU_4.G AS G FROM Edge_TU AS Edge_TU_4
    F: SELECT Edge_UF_4.a_0 AS y, Edge_UF_4.a_1 AS z, Edge_UF_4.G AS G FROM Edge_UF AS Edge_UF_4
    G : SELECT Edge_G_4.a_0 AS y, Edge_G_4.a_1 AS z, Edge_G_4.G AS G FROM Edge_G AS Edge_G_4
 - (not (Edge y z)):
    T: SELECT Edge_UF_4.a_0 AS y, Edge_UF_4.a_1 AS z, "true" AS G FROM Edge_UF AS Edge_UF_4
    F: SELECT Edge_TU_4.a_0 AS y, Edge_TU_4.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_4
    G : SELECT Edge_G_4.a_0 AS y, Edge_G_4.a_1 AS z, not_(Edge_G_4.G) AS G FROM Edge_G AS Edge_G_4
 - (Edge x z):
    T: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, Edge_TU_7.G AS G FROM Edge_TU AS Edge_TU_7
    F: SELECT Edge_UF_7.a_0 AS x, Edge_UF_7.a_1 AS z, Edge_UF_7.G AS G FROM Edge_UF AS Edge_UF_7
    G : SELECT Edge_G_7.a_0 AS x, Edge_G_7.a_1 AS z, Edge_G_7.G AS G FROM Edge_G AS Edge_G_7
 - (not (Edge x z)):
    T: SELECT Edge_UF_7.a_0 AS x, Edge_UF_7.a_1 AS z, "true" AS G FROM Edge_UF AS Edge_UF_7
    F: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_7
    G : SELECT Edge_G_7.a_0 AS x, Edge_G_7.a_1 AS z, not_(Edge_G_7.G) AS G FROM Edge_G AS Edge_G_7
 - (phi x y z):
    TU: SELECT Node.G AS x, Node_1.G AS y, Node_4.G AS z, apply("phi", Node.G, Node_1.G, Node_4.G) AS G FROM Node JOIN Node AS Node_1 JOIN Node AS Node_4
    UF: SELECT Node.G AS x, Node_1.G AS y, Node_4.G AS z, apply("phi", Node.G, Node_1.G, Node_4.G) AS G FROM Node JOIN Node AS Node_1 JOIN Node AS Node_4
    G : SELECT Node.G AS x, Node_1.G AS y, Node_4.G AS z, apply("phi", Node.G, Node_1.G, Node_4.G) AS G FROM Node JOIN Node AS Node_1 JOIN Node AS Node_4
 - (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z)):
    TU: SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G_4.a_1 AS z, or_(not_(Edge_G.G), not_(Edge_G_4.G), not_(Edge_G_7.G), apply("phi", Edge_G.a_0, Edge_G.a_1, Edge_G_4.a_1)) AS G FROM Edge_G AS Edge_G JOIN Edge_G AS Edge_G_4 ON Edge_G.a_1 = Edge_G_4.a_0 JOIN Edge_G AS Edge_G_7 ON Edge_G.a_0 = Edge_G_7.a_0 AND Edge_G_4.a_1 = Edge_G_7.a_1
    UF: SELECT Edge_TU.a_0 AS x, Edge_TU.a_1 AS y, Edge_TU_4.a_1 AS z, apply("phi", Edge_TU.a_0, Edge_TU.a_1, Edge_TU_4.a_1) AS G FROM Edge_TU AS Edge_TU JOIN Edge_TU AS Edge_TU_4 ON Edge_TU.a_1 = Edge_TU_4.a_0 JOIN Edge_TU AS Edge_TU_7 ON Edge_TU.a_0 = Edge_TU_7.a_0 AND Edge_TU_4.a_1 = Edge_TU_7.a_1
    G : SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G_4.a_1 AS z, or_(not_(Edge_G.G), not_(Edge_G_4.G), not_(Edge_G_7.G), apply("phi", Edge_G.a_0, Edge_G.a_1, Edge_G_4.a_1)) AS G FROM Edge_G AS Edge_G JOIN Edge_G AS Edge_G_4 ON Edge_G.a_1 = Edge_G_4.a_0 JOIN Edge_G AS Edge_G_7 ON Edge_G.a_0 = Edge_G_7.a_0 AND Edge_G_4.a_1 = Edge_G_7.a_1
 - (forall ((x Node) (y Node) (z Node)) (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z))):
    TU: SELECT Agg_0_TU.G AS G FROM Agg_0_TU
    UF: SELECT Agg_0_UF.G AS G FROM Agg_0_UF
    G : SELECT Agg_0_G.G AS G FROM Agg_0_G
 - (Edge x x):
    T: SELECT Edge_TU_12.a_1 AS x, Edge_TU_12.G AS G FROM Edge_TU AS Edge_TU_12 WHERE Edge_TU_12.a_1 = Edge_TU_12.a_0
    F: SELECT Edge_UF_12.a_1 AS x, Edge_UF_12.G AS G FROM Edge_UF AS Edge_UF_12 WHERE Edge_UF_12.a_1 = Edge_UF_12.a_0
    G : SELECT Edge_G_12.a_1 AS x, Edge_G_12.G AS G FROM Edge_G AS Edge_G_12 WHERE Edge_G_12.a_1 = Edge_G_12.a_0
 - (forall ((x Node)) (Edge x x)):
    TU: SELECT Agg_12_TU.G AS G FROM Agg_12_TU
    UF: SELECT Agg_12_UF.G AS G FROM Agg_12_UF
    G : SELECT Agg_12_G.G AS G FROM Agg_12_G
 - (exists ((x Node) (y Node)) (Edge x y)):
    TU: SELECT Agg_14_TU.G AS G FROM Agg_14_TU
    UF: SELECT Agg_14_UF.G AS G FROM Agg_14_UF
    G : SELECT Agg_14_G.G AS G FROM Agg_14_G
(check-sat)