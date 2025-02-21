(set-option :backend none)
(declare-datatype T ( ( a ) ( b ) ))
(declare-fun p (T T) Bool)
(x-interpret-pred p (a a))
(declare-fun f (T) T)
(assert (forall ((x T)) (and (p x (f a)) (p x (f b)))))
(x-ground)
(x-debug db p_TU)
(x-debug db-view Agg_0_TU)
(x-debug solver groundings)
-------------------------

(declare-datatype T ((a ) (b )))
(declare-fun p (T T) Bool)
(x-interpret-pred p (a a))
(declare-fun f (T) T)

(push)
(assert (forall ((x T)) (and (p x (f a)) (p x (f b)))))
(pop)
(assert (=> (= (f a) a) (= (f b) a) true))
(assert (=> (= (f a) a) (= (f b) b) false))
(assert (=> (= (f a) b) (= (f b) a) false))
(assert (=> (= (f a) b) (= (f b) b) false))
(assert (=> (= (f a) a) (= (f b) a) false))
(assert (=> (= (f a) a) (= (f b) b) false))
(assert (=> (= (f a) b) (= (f b) a) false))
(assert (=> (= (f a) b) (= (f b) b) false))
 TABLE: p_TU
┌─────┬─────┬────────┐
│ a_0 │ a_1 │ G      │
├─────┼─────┼────────┤
│ "a" │ "a" │ "true" │
└─────┴─────┴────────┘
CREATE VIEW Agg_0_TU AS SELECT and_aggregate(G) as G from (SELECT p_G.a_0 AS x, apply("=>", apply("=",apply("f", "a"), p_G.a_1), apply("=",apply("f", "b"), p_G_4.a_1), and_(p_G.G, p_G_4.G)) AS G FROM p_G AS p_G JOIN p_G AS p_G_4 ON p_G.a_0 = p_G_4.a_0) HAVING and_aggregate(G) <> false
Groundings:
 - x: SELECT T.G AS x, T.G AS G FROM T
 - a: SELECT "a" AS G
 - (f a): SELECT apply("f", "a") AS G
 - (p x (f a)):
    TU: SELECT p_TU.a_0 AS x, (apply("=",apply("f", "a"), p_TU.a_1)) AS cond, p_TU.G AS G FROM p_TU AS p_TU
    UF: SELECT p_UF.a_0 AS x, (apply("=",apply("f", "a"), p_UF.a_1)) AS cond, p_UF.G AS G FROM p_UF AS p_UF
    G : SELECT p_G.a_0 AS x, (apply("=",apply("f", "a"), p_G.a_1)) AS cond, p_G.G AS G FROM p_G AS p_G
 - b: SELECT "b" AS G
 - (f b): SELECT apply("f", "b") AS G
 - (p x (f b)):
    TU: SELECT p_TU_4.a_0 AS x, (apply("=",apply("f", "b"), p_TU_4.a_1)) AS cond, p_TU_4.G AS G FROM p_TU AS p_TU_4
    UF: SELECT p_UF_4.a_0 AS x, (apply("=",apply("f", "b"), p_UF_4.a_1)) AS cond, p_UF_4.G AS G FROM p_UF AS p_UF_4
    G : SELECT p_G_4.a_0 AS x, (apply("=",apply("f", "b"), p_G_4.a_1)) AS cond, p_G_4.G AS G FROM p_G AS p_G_4
 - (and (p x (f a)) (p x (f b))):
    TU: SELECT p_TU.a_0 AS x, and_((apply("=",apply("f", "a"), p_TU.a_1)), (apply("=",apply("f", "b"), p_TU_4.a_1))) AS cond, and_(p_TU.G, p_TU_4.G) AS G FROM p_TU AS p_TU JOIN p_TU AS p_TU_4 ON p_TU.a_0 = p_TU_4.a_0
    UF: SELECT p_G.a_0 AS x, and_((apply("=",apply("f", "a"), p_G.a_1)), (apply("=",apply("f", "b"), p_G_4.a_1))) AS cond, and_(p_G.G, p_G_4.G) AS G FROM p_G AS p_G JOIN p_G AS p_G_4 ON p_G.a_0 = p_G_4.a_0
    G : SELECT p_G.a_0 AS x, and_((apply("=",apply("f", "a"), p_G.a_1)), (apply("=",apply("f", "b"), p_G_4.a_1))) AS cond, and_(p_G.G, p_G_4.G) AS G FROM p_G AS p_G JOIN p_G AS p_G_4 ON p_G.a_0 = p_G_4.a_0
 - (forall ((x T)) (and (p x (f a)) (p x (f b)))):
    TU: SELECT Agg_0_TU.G AS G FROM Agg_0_TU
    UF: SELECT Agg_0_UF.G AS G FROM Agg_0_UF
    G : SELECT Agg_0_G.G AS G FROM Agg_0_G