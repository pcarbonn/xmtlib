(set-option :backend none)
(declare-datatype T ( ( a ) ( b ) ))
(declare-fun p (T T) Bool)
(x-interpret-pred p (a a))
(declare-fun f (T) T)
(assert (forall ((x T)) (not (p x (f a)))))
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
(assert (forall ((x T)) (not (p x (f a)))))
(pop)
(assert (not (= (f a) a)))
 TABLE: p_TU
┌─────┬─────┬────────┐
│ a_0 │ a_1 │ G      │
├─────┼─────┼────────┤
│ "a" │ "a" │ "true" │
└─────┴─────┴────────┘
CREATE VIEW Agg_0_TU AS SELECT and_aggregate(implies_(if_, G)) as G from (SELECT p_G.a_0 AS x, (apply("=",apply("f", "a"), p_G.a_1)) AS if_, not_(p_G.G) AS G FROM p_G AS p_G) HAVING and_aggregate(implies_(if_, G)) <> false
Groundings:
 - x: SELECT T.G AS x, T.G AS G FROM T
 - a: SELECT "a" AS G
 - (f a): SELECT apply("f", "a") AS G
 - (p x (f a)):
    TU: SELECT p_TU.a_0 AS x, (apply("=",apply("f", "a"), p_TU.a_1)) AS if_, p_TU.G AS G FROM p_TU AS p_TU
    UF: SELECT p_UF.a_0 AS x, (apply("=",apply("f", "a"), p_UF.a_1)) AS if_, p_UF.G AS G FROM p_UF AS p_UF
    G : SELECT p_G.a_0 AS x, (apply("=",apply("f", "a"), p_G.a_1)) AS if_, p_G.G AS G FROM p_G AS p_G
 - (not (p x (f a))):
    TU: SELECT p_UF.a_0 AS x, (apply("=",apply("f", "a"), p_UF.a_1)) AS if_, not_(p_UF.G) AS G FROM p_UF AS p_UF
    UF: SELECT p_TU.a_0 AS x, (apply("=",apply("f", "a"), p_TU.a_1)) AS if_, not_(p_TU.G) AS G FROM p_TU AS p_TU
    G : SELECT p_G.a_0 AS x, (apply("=",apply("f", "a"), p_G.a_1)) AS if_, not_(p_G.G) AS G FROM p_G AS p_G
 - (forall ((x T)) (not (p x (f a)))):
    TU: SELECT Agg_0_TU.G AS G FROM Agg_0_TU
    UF: SELECT Agg_0_UF.G AS G FROM Agg_0_UF
    G : SELECT Agg_0_G.G AS G FROM Agg_0_G