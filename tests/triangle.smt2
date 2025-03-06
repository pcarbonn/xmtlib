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
CREATE VIEW Agg_14_UF AS SELECT or_aggregate(G) as G from (SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_2.G AS G FROM Edge_G AS Edge_G_2) HAVING or_aggregate(G) <> "true"
Groundings:
 - x: SELECT Node.G AS x, Node.G AS G FROM Node
 - y: SELECT Node_1.G AS y, Node_1.G AS G FROM Node AS Node_1
 - (Edge x y):
    T: SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, "true" AS G FROM Edge_TU AS Edge_TU_2
    F: SELECT Edge_UF_2.a_0 AS x, Edge_UF_2.a_1 AS y, "false" AS G FROM Edge_UF AS Edge_UF_2
    G : SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_2.G AS G FROM Edge_G AS Edge_G_2
 - (not (Edge x y)):
    T: SELECT Edge_UF_2.a_0 AS x, Edge_UF_2.a_1 AS y, "true" AS G FROM Edge_UF AS Edge_UF_2
    F: SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, "false" AS G FROM Edge_TU AS Edge_TU_2
    G : SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, not_(Edge_G_2.G) AS G FROM Edge_G AS Edge_G_2
 - z: SELECT Node_4.G AS z, Node_4.G AS G FROM Node AS Node_4
 - (Edge y z):
    T: SELECT Edge_TU_5.a_0 AS y, Edge_TU_5.a_1 AS z, "true" AS G FROM Edge_TU AS Edge_TU_5
    F: SELECT Edge_UF_5.a_0 AS y, Edge_UF_5.a_1 AS z, "false" AS G FROM Edge_UF AS Edge_UF_5
    G : SELECT Edge_G_5.a_0 AS y, Edge_G_5.a_1 AS z, Edge_G_5.G AS G FROM Edge_G AS Edge_G_5
 - (not (Edge y z)):
    T: SELECT Edge_UF_5.a_0 AS y, Edge_UF_5.a_1 AS z, "true" AS G FROM Edge_UF AS Edge_UF_5
    F: SELECT Edge_TU_5.a_0 AS y, Edge_TU_5.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_5
    G : SELECT Edge_G_5.a_0 AS y, Edge_G_5.a_1 AS z, not_(Edge_G_5.G) AS G FROM Edge_G AS Edge_G_5
 - (Edge x z):
    T: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, "true" AS G FROM Edge_TU AS Edge_TU_7
    F: SELECT Edge_UF_7.a_0 AS x, Edge_UF_7.a_1 AS z, "false" AS G FROM Edge_UF AS Edge_UF_7
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
    TU: SELECT x, y, z, or_aggregate(G) as G from (SELECT negate_3.x AS x, negate_3.y AS y, Node_4.z AS z, negate_3.G AS G FROM negate AS negate_3 JOIN Node AS Node_4 UNION SELECT Node.x AS x, negate_6.y AS y, negate_6.z AS z, negate_6.G AS G FROM negate AS negate_6 JOIN Node UNION SELECT negate_8.x AS x, Node_1.y AS y, negate_8.z AS z, negate_8.G AS G FROM negate AS negate_8 JOIN Node AS Node_1 UNION SELECT phi_9.x AS x, phi_9.y AS y, phi_9.z AS z, phi_9.G AS G FROM phi AS phi_9) GROUP BY x, y, z
    UF: SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, Edge_TU_5.a_1 AS z, apply("phi", Edge_TU_2.a_0, Edge_TU_2.a_1, Edge_TU_5.a_1) AS G FROM Edge_TU AS Edge_TU_2 JOIN Edge_TU AS Edge_TU_5 ON Edge_TU_2.a_1 = Edge_TU_5.a_0 JOIN Edge_TU AS Edge_TU_7 ON Edge_TU_2.a_0 = Edge_TU_7.a_0 AND Edge_TU_5.a_1 = Edge_TU_7.a_1
    G : SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_5.a_1 AS z, or_(not_(Edge_G_2.G), not_(Edge_G_5.G), not_(Edge_G_7.G), apply("phi", Edge_G_2.a_0, Edge_G_2.a_1, Edge_G_5.a_1)) AS G FROM Edge_G AS Edge_G_2 JOIN Edge_G AS Edge_G_5 ON Edge_G_2.a_1 = Edge_G_5.a_0 JOIN Edge_G AS Edge_G_7 ON Edge_G_2.a_0 = Edge_G_7.a_0 AND Edge_G_5.a_1 = Edge_G_7.a_1
 - (forall ((x Node) (y Node) (z Node)) (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z))):
    TU: SELECT and_aggregate(G) as G from (SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_5.a_1 AS z, or_(not_(Edge_G_2.G), not_(Edge_G_5.G), not_(Edge_G_7.G), apply("phi", Edge_G_2.a_0, Edge_G_2.a_1, Edge_G_5.a_1)) AS G FROM Edge_G AS Edge_G_2 JOIN Edge_G AS Edge_G_5 ON Edge_G_2.a_1 = Edge_G_5.a_0 JOIN Edge_G AS Edge_G_7 ON Edge_G_2.a_0 = Edge_G_7.a_0 AND Edge_G_5.a_1 = Edge_G_7.a_1) HAVING and_aggregate(G) <> "false"
    UF: SELECT G as G from (SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, Edge_TU_5.a_1 AS z, apply("phi", Edge_TU_2.a_0, Edge_TU_2.a_1, Edge_TU_5.a_1) AS G FROM Edge_TU AS Edge_TU_2 JOIN Edge_TU AS Edge_TU_5 ON Edge_TU_2.a_1 = Edge_TU_5.a_0 JOIN Edge_TU AS Edge_TU_7 ON Edge_TU_2.a_0 = Edge_TU_7.a_0 AND Edge_TU_5.a_1 = Edge_TU_7.a_1)
    G : SELECT and_aggregate(G) as G from (SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_5.a_1 AS z, or_(not_(Edge_G_2.G), not_(Edge_G_5.G), not_(Edge_G_7.G), apply("phi", Edge_G_2.a_0, Edge_G_2.a_1, Edge_G_5.a_1)) AS G FROM Edge_G AS Edge_G_2 JOIN Edge_G AS Edge_G_5 ON Edge_G_2.a_1 = Edge_G_5.a_0 JOIN Edge_G AS Edge_G_7 ON Edge_G_2.a_0 = Edge_G_7.a_0 AND Edge_G_5.a_1 = Edge_G_7.a_1)
 - (Edge x x):
    T: SELECT Edge_TU_12.a_1 AS x, "true" AS G FROM Edge_TU AS Edge_TU_12 WHERE Edge_TU_12.a_1 = Edge_TU_12.a_0
    F: SELECT Edge_UF_12.a_1 AS x, "false" AS G FROM Edge_UF AS Edge_UF_12 WHERE Edge_UF_12.a_1 = Edge_UF_12.a_0
    G : SELECT Edge_G_12.a_1 AS x, Edge_G_12.G AS G FROM Edge_G AS Edge_G_12 WHERE Edge_G_12.a_1 = Edge_G_12.a_0
 - (forall ((x Node)) (Edge x x)):
    TU: SELECT and_aggregate(G) as G from (SELECT Edge_G_12.a_1 AS x, Edge_G_12.G AS G FROM Edge_G AS Edge_G_12 WHERE Edge_G_12.a_1 = Edge_G_12.a_0) HAVING and_aggregate(G) <> "false"
    UF: SELECT G as G from (SELECT Edge_UF_12.a_1 AS x, "false" AS G FROM Edge_UF AS Edge_UF_12 WHERE Edge_UF_12.a_1 = Edge_UF_12.a_0)
    G : SELECT and_aggregate(G) as G from (SELECT Edge_G_12.a_1 AS x, Edge_G_12.G AS G FROM Edge_G AS Edge_G_12 WHERE Edge_G_12.a_1 = Edge_G_12.a_0)
 - (exists ((x Node) (y Node)) (Edge x y)):
    TU: SELECT or_aggregate(G) as G from (SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, "true" AS G FROM Edge_TU AS Edge_TU_2)
    UF: SELECT or_aggregate(G) as G from (SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_2.G AS G FROM Edge_G AS Edge_G_2) HAVING or_aggregate(G) <> "true"
    G : SELECT or_aggregate(G) as G from (SELECT Edge_G_2.a_0 AS x, Edge_G_2.a_1 AS y, Edge_G_2.G AS G FROM Edge_G AS Edge_G_2)
(check-sat)