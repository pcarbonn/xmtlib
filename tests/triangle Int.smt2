(set-option :backend none)
(declare-fun Edge (Int Int) Bool)
(declare-fun phi (Int Int Int) Bool)
(x-interpret-pred Edge
    (1 2)
    (2 3)
    (1 3)
)
(assert (forall ((x Int) (y Int) (z Int))
            (=> (and (Edge x y) (Edge y z) (Edge x z))
                     (phi x y z)
            )))
(x-ground)
(x-debug solver functions)
;(x-debug db-view Edge_UF)
(x-debug solver groundings)
(check-sat)
-------------------------

(declare-fun Edge (Int Int) Bool)
(declare-fun phi (Int Int Int) Bool)
(x-interpret-pred Edge (1 2) (2 3) (1 3))

(push)
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (Edge x y) (Edge y z) (Edge x z)) (phi x y z))))
(pop)
(assert (forall ((x Int) (y Int) (z Int)) (phi 1 2 3)))
Functions:
 - true: Constructed
 - false: Constructed
 - not: Predefined (true)
 - =>: Predefined (true)
 - and: Predefined (true)
 - or: Predefined (true)
 - xor: Predefined (true)
 - =: Predefined (true)
 - distinct: Predefined (true)
 - <=: Predefined (true)
 - <: Predefined (true)
 - >=: Predefined (true)
 - >: Predefined (true)
 - ite: Predefined (?)
 - +: Predefined (false)
 - -: Predefined (false)
 - *: Predefined (false)
 - div: Predefined (false)
 - mod: Predefined (false)
 - abs: Predefined (false)
 - Edge: Boolean (Edge_TU Complete, (infinite), (infinite))
 - phi: Int * Int * Int -> Bool (true)
Groundings:
 - x: SELECT "x" AS x, "x" AS G
 - y: SELECT "y" AS y, "y" AS G
 - (Edge x y):
    T: SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, "true" AS G FROM Edge_TU AS Edge_TU_2
    UF: SELECT "x" AS x, "y" AS y, apply("Edge", "x", "y") AS G
    G : SELECT "x" AS x, "y" AS y, apply("Edge", "x", "y") AS G
 - (not (Edge x y)):
    TU: SELECT "x" AS x, "y" AS y, apply("not", apply("Edge", "x", "y")) AS G
    F: SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, "false" AS G FROM Edge_TU AS Edge_TU_2
    G : SELECT "x" AS x, "y" AS y, apply("not", apply("Edge", "x", "y")) AS G
 - z: SELECT "z" AS z, "z" AS G
 - (Edge y z):
    T: SELECT Edge_TU_5.a_0 AS y, Edge_TU_5.a_1 AS z, "true" AS G FROM Edge_TU AS Edge_TU_5
    UF: SELECT "y" AS y, "z" AS z, apply("Edge", "y", "z") AS G
    G : SELECT "y" AS y, "z" AS z, apply("Edge", "y", "z") AS G
 - (not (Edge y z)):
    TU: SELECT "y" AS y, "z" AS z, apply("not", apply("Edge", "y", "z")) AS G
    F: SELECT Edge_TU_5.a_0 AS y, Edge_TU_5.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_5
    G : SELECT "y" AS y, "z" AS z, apply("not", apply("Edge", "y", "z")) AS G
 - (Edge x z):
    T: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, "true" AS G FROM Edge_TU AS Edge_TU_7
    UF: SELECT "x" AS x, "z" AS z, apply("Edge", "x", "z") AS G
    G : SELECT "x" AS x, "z" AS z, apply("Edge", "x", "z") AS G
 - (not (Edge x z)):
    TU: SELECT "x" AS x, "z" AS z, apply("not", apply("Edge", "x", "z")) AS G
    F: SELECT Edge_TU_7.a_0 AS x, Edge_TU_7.a_1 AS z, "false" AS G FROM Edge_TU AS Edge_TU_7
    G : SELECT "x" AS x, "z" AS z, apply("not", apply("Edge", "x", "z")) AS G
 - (phi x y z):
    TU: SELECT "x" AS x, "y" AS y, "z" AS z, apply("phi", "x", "y", "z") AS G
    UF: SELECT "x" AS x, "y" AS y, "z" AS z, apply("phi", "x", "y", "z") AS G
    G : SELECT "x" AS x, "y" AS y, "z" AS z, apply("phi", "x", "y", "z") AS G
 - (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z)):
    TU: SELECT x, y, z, or_aggregate(G) as G from (SELECT "x" AS x, "y" AS y, "z" AS z, apply("not", apply("Edge", "x", "y")) AS G UNION SELECT "x" AS x, "y" AS y, "z" AS z, apply("not", apply("Edge", "y", "z")) AS G UNION SELECT "x" AS x, "y" AS y, "z" AS z, apply("not", apply("Edge", "x", "z")) AS G UNION SELECT "x" AS x, "y" AS y, "z" AS z, apply("phi", "x", "y", "z") AS G)
    UF: SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, Edge_TU_5.a_1 AS z, apply("phi", Edge_TU_2.a_0, Edge_TU_2.a_1, Edge_TU_5.a_1) AS G FROM Edge_TU AS Edge_TU_2 JOIN Edge_TU AS Edge_TU_5 ON Edge_TU_2.a_1 = Edge_TU_5.a_0 JOIN Edge_TU AS Edge_TU_7 ON Edge_TU_2.a_0 = Edge_TU_7.a_0 AND Edge_TU_5.a_1 = Edge_TU_7.a_1
    G : SELECT "x" AS x, "y" AS y, "z" AS z, apply("or", apply("not", apply("Edge", "x", "y")), apply("not", apply("Edge", "y", "z")), apply("not", apply("Edge", "x", "z")), apply("phi", "x", "y", "z")) AS G
 - (forall ((x Int) (y Int) (z Int)) (or (not (Edge x y)) (not (Edge y z)) (not (Edge x z)) (phi x y z))):
    TU: SELECT "(forall ((x Int) (y Int) (z Int)) " || and_aggregate(G) || ")" as G from (SELECT "x" AS x, "y" AS y, "z" AS z, apply("or", apply("not", apply("Edge", "x", "y")), apply("not", apply("Edge", "y", "z")), apply("not", apply("Edge", "x", "z")), apply("phi", "x", "y", "z")) AS G)
    UF: SELECT "(forall ((x Int) (y Int) (z Int)) " || G || ")" as G from (SELECT Edge_TU_2.a_0 AS x, Edge_TU_2.a_1 AS y, Edge_TU_5.a_1 AS z, apply("phi", Edge_TU_2.a_0, Edge_TU_2.a_1, Edge_TU_5.a_1) AS G FROM Edge_TU AS Edge_TU_2 JOIN Edge_TU AS Edge_TU_5 ON Edge_TU_2.a_1 = Edge_TU_5.a_0 JOIN Edge_TU AS Edge_TU_7 ON Edge_TU_2.a_0 = Edge_TU_7.a_0 AND Edge_TU_5.a_1 = Edge_TU_7.a_1)
    G : SELECT "(forall ((x Int) (y Int) (z Int)) " || and_aggregate(G) || ")" as G from (SELECT "x" AS x, "y" AS y, "z" AS z, apply("or", apply("not", apply("Edge", "x", "y")), apply("not", apply("Edge", "y", "z")), apply("not", apply("Edge", "x", "z")), apply("phi", "x", "y", "z")) AS G)
(check-sat)