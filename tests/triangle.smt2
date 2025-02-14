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
(x-ground)
;(x-debug db-view Agg_0_UF)
(x-debug solver groundings)
(check-sat)
-------------------------



(x-interpret-pred Edge (|1| |2|) (|2| |3|) (|1| |3|))





Groundings:
 - x: SELECT Node.G AS x, Node.G AS G FROM Node
 - y: SELECT Node_1.G AS y, Node_1.G AS G FROM Node AS Node_1
 - (Edge x y):
    TU: SELECT Edge_TU.a_0 AS x, Edge_TU.a_1 AS y, Edge_TU.G AS G FROM Edge_TU AS Edge_TU
    UF: SELECT Edge_UF.a_0 AS x, Edge_UF.a_1 AS y, Edge_UF.G AS G FROM Edge_UF AS Edge_UF
    G : SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G.G AS G FROM Edge_G AS Edge_G
 - (not (Edge x y)):
    TU: SELECT Edge_UF.a_0 AS x, Edge_UF.a_1 AS y, "true" AS G FROM Edge_UF AS Edge_UF
    UF: SELECT Edge_TU.a_0 AS x, Edge_TU.a_1 AS y, "false" AS G FROM Edge_TU AS Edge_TU
    G : SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, apply("not", Edge_G.G) AS G FROM Edge_G AS Edge_G
 - z: SELECT Node_4.G AS z, Node_4.G AS G FROM Node AS Node_4
 - (Edge y z):
    TU: SELECT Edge_TU_4.a_0 AS y, Edge_TU_4.a_1 AS z, Edge_TU_4.G AS G FROM Edge_TU AS Edge_TU_4
    UF: SELECT Edge_UF_4.a_0 AS y, Edge_UF_4.a_1 AS z, Edge_UF_4.G AS G FROM Edge_UF AS Edge_UF_4
    G : SELECT Edge_G_4.a_0 AS y, Edge_G_4.a_1 AS z, Edge_G_4.G AS G FROM Edge_G AS Edge_G_4
 - (not (Edge y z)):
    TU: SELECT Edge_UF_4.a_0 AS y, Edge_UF_4.a_1 AS z, "true" AS G FROM Edge_UF AS Edge_UF_4
    UF: SELECT Edge_TU_4.a_0 AS y, Edge_TU_4.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_4
    G : SELECT Edge_G_4.a_0 AS y, Edge_G_4.a_1 AS z, apply("not", Edge_G_4.G) AS G FROM Edge_G AS Edge_G_4
 - (Edge x z):
    TU: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, Edge_TU_7.G AS G FROM Edge_TU AS Edge_TU_7
    UF: SELECT Edge_UF_7.a_0 AS x, Edge_UF_7.a_1 AS z, Edge_UF_7.G AS G FROM Edge_UF AS Edge_UF_7
    G : SELECT Edge_G_7.a_0 AS x, Edge_G_7.a_1 AS z, Edge_G_7.G AS G FROM Edge_G AS Edge_G_7
 - (not (Edge x z)):
    TU: SELECT Edge_UF_7.a_0 AS x, Edge_UF_7.a_1 AS z, "true" AS G FROM Edge_UF AS Edge_UF_7
    UF: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_7
    G : SELECT Edge_G_7.a_0 AS x, Edge_G_7.a_1 AS z, apply("not", Edge_G_7.G) AS G FROM Edge_G AS Edge_G_7
 - (phi x y z):
    TU: SELECT Node.G AS x, Node_1.G AS y, Node_4.G AS z, apply("phi", Node.G, Node_1.G, Node_4.G) AS G FROM Node JOIN Node AS Node_1 JOIN Node AS Node_4
    UF: SELECT Node.G AS x, Node_1.G AS y, Node_4.G AS z, apply("phi", Node.G, Node_1.G, Node_4.G) AS G FROM Node JOIN Node AS Node_1 JOIN Node AS Node_4
    G : SELECT Node.G AS x, Node_1.G AS y, Node_4.G AS z, apply("phi", Node.G, Node_1.G, Node_4.G) AS G FROM Node JOIN Node AS Node_1 JOIN Node AS Node_4
 - (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z)):
    TU: SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G_4.a_1 AS z, apply("or", apply("not", Edge_G.G), apply("not", Edge_G_4.G), apply("not", Edge_G_7.G), apply("phi", Edge_G.a_0, Edge_G.a_1, Edge_G_4.a_1)) AS G
    UF: SELECT Edge_TU.a_0 AS x, Edge_TU.a_1 AS y, Edge_TU_4.a_1 AS z, apply("phi", Edge_TU.a_0, Edge_TU.a_1, Edge_TU_4.a_1) AS G FROM Edge_TU AS Edge_TU JOIN Edge_TU AS Edge_TU_4 ON Edge_TU.a_1 = Edge_TU_4.a_0 JOIN Edge_TU AS Edge_TU_7 ON Edge_TU.a_0 = Edge_TU_7.a_0 AND Edge_TU_4.a_1 = Edge_TU_7.a_1
    G : SELECT Edge_G.a_0 AS x, Edge_G.a_1 AS y, Edge_G_4.a_1 AS z, apply("or", apply("not", Edge_G.G), apply("not", Edge_G_4.G), apply("not", Edge_G_7.G), apply("phi", Edge_G.a_0, Edge_G.a_1, Edge_G_4.a_1)) AS G FROM Edge_G AS Edge_G JOIN Edge_G AS Edge_G_4 ON Edge_G.a_1 = Edge_G_4.a_0 JOIN Edge_G AS Edge_G_7 ON Edge_G.a_0 = Edge_G_7.a_0 AND Edge_G_4.a_1 = Edge_G_7.a_1
 - (forall () (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z))):
    TU: SELECT Agg_0_TU.G AS G FROM Agg_0_TU
    UF: SELECT Agg_0_UF.G AS G FROM Agg_0_UF
    G : SELECT Agg_0_G.G AS G FROM Agg_0_G
sat
