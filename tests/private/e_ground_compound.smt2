(set-option :backend none)
(declare-datatype T ( ( a ) ( b ) ))
(declare-fun p (T T) Bool)
(x-interpret-pred p (a a))
(declare-fun f (T) T)
(assert (p a a))
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
(assert (p a a))
(pop)
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
****** Database Error: Query returned no rows
Groundings:
 - a: SELECT "a" AS G
 - (p a a):
    T: SELECT "true" AS G FROM p_TU AS p_TU_1 WHERE "a" = p_TU_1.a_0 AND "a" = p_TU_1.a_1
    F: SELECT "false" AS G FROM p_UF AS p_UF_1 WHERE "a" = p_UF_1.a_0 AND "a" = p_UF_1.a_1
    G : SELECT p_G_1.G AS G FROM p_G AS p_G_1 WHERE "a" = p_G_1.a_0 AND "a" = p_G_1.a_1
 - x: SELECT T_2.G AS x, T_2.G AS G FROM T AS T_2
 - (f a): SELECT apply("f", "a") AS G
 - (p x (f a)):
    T: SELECT p_TU_4.a_0 AS x, apply("=",apply("f", "a"), p_TU_4.a_1) AS if_, "true" AS G FROM p_TU AS p_TU_4
    F: SELECT p_UF_4.a_0 AS x, apply("=",apply("f", "a"), p_UF_4.a_1) AS if_, "false" AS G FROM p_UF AS p_UF_4
    G : SELECT p_G_4.a_0 AS x, apply("=",apply("f", "a"), p_G_4.a_1) AS if_, p_G_4.G AS G FROM p_G AS p_G_4
 - (not (p x (f a))):
    T: SELECT p_UF_4.a_0 AS x, apply("=",apply("f", "a"), p_UF_4.a_1) AS if_, "true" AS G FROM p_UF AS p_UF_4
    F: SELECT p_TU_4.a_0 AS x, apply("=",apply("f", "a"), p_TU_4.a_1) AS if_, "false" AS G FROM p_TU AS p_TU_4
    G : SELECT p_G_4.a_0 AS x, apply("=",apply("f", "a"), p_G_4.a_1) AS if_, not_(p_G_4.G) AS G FROM p_G AS p_G_4
 - (forall ((x T)) (not (p x (f a)))):
    TU: SELECT and_aggregate(implies_(if_, G)) as G from (SELECT p_G_4.a_0 AS x, apply("=",apply("f", "a"), p_G_4.a_1) AS if_, not_(p_G_4.G) AS G FROM p_G AS p_G_4)
    UF: SELECT implies_(if_, G) as G from (SELECT p_TU_4.a_0 AS x, apply("=",apply("f", "a"), p_TU_4.a_1) AS if_, "false" AS G FROM p_TU AS p_TU_4)
    G : SELECT and_aggregate(implies_(if_, G)) as G from (SELECT p_G_4.a_0 AS x, apply("=",apply("f", "a"), p_G_4.a_1) AS if_, not_(p_G_4.G) AS G FROM p_G AS p_G_4)