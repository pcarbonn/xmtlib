(set-option :backend none)
(assert false)
(assert (and true true))
(assert (or false false))


(declare-fun is_true (Bool) Bool)
(x-interpret-pred is_true (true))
(assert (is_true true))
(assert (not (and (is_true true) (is_true false))))
(assert (not (is_true (exists ((x Bool)) (is_true x)))))

(x-ground)
(x-debug solver groundings)
(x-debug db is_true_UF)
-------------------------
(declare-fun is_true (Bool) Bool)
(assert false)
(assert false)
(assert false)
Groundings:
 - false:
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G
    G : SELECT "false" AS G
 - true:
    T: SELECT "true" AS G
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (and true true):
    T: SELECT "true" AS G
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT "true" AS G
 - (or false false):
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G
    G : SELECT "false" AS G
 - (is_true true):
    T: SELECT "true" AS G FROM is_true_TU AS is_true_TU_4 WHERE "true" = is_true_TU_4.a_0
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT is_true_G_4.G AS G FROM is_true_G AS is_true_G_4 WHERE "true" = is_true_G_4.a_0
 - (not (is_true true)):
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G FROM is_true_TU AS is_true_TU_4 WHERE "true" = is_true_TU_4.a_0
    G : SELECT not_(is_true_G_4.G) AS G FROM is_true_G AS is_true_G_4 WHERE "true" = is_true_G_4.a_0
 - (is_true false):
    T: SELECT "true" AS G WHERE FALSE
    F: SELECT "false" AS G FROM is_true_UF AS is_true_UF_6 WHERE "false" = is_true_UF_6.a_0
    G : SELECT is_true_G_6.G AS G FROM is_true_G AS is_true_G_6 WHERE "false" = is_true_G_6.a_0
 - (not (is_true false)):
    T: SELECT "true" AS G FROM is_true_UF AS is_true_UF_6 WHERE "false" = is_true_UF_6.a_0
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT not_(is_true_G_6.G) AS G FROM is_true_G AS is_true_G_6 WHERE "false" = is_true_G_6.a_0
 - (or (not (is_true true)) (not (is_true false))):
    T: SELECT negate_7.G AS G FROM negate_7
    F: SELECT "true" AS G WHERE FALSE
    G : SELECT or_(not_(is_true_G_4.G), not_(is_true_G_6.G)) AS G FROM is_true_G AS is_true_G_4 JOIN is_true_G AS is_true_G_6 ON "false" = is_true_G_6.a_0 WHERE "true" = is_true_G_4.a_0
 - x: SELECT Bool_9.G AS x, Bool_9.G AS G FROM Bool AS Bool_9
 - (is_true x):
    T: SELECT is_true_TU_10.a_0 AS x, "true" AS G FROM is_true_TU AS is_true_TU_10
    F: SELECT is_true_UF_10.a_0 AS x, "false" AS G FROM is_true_UF AS is_true_UF_10
    G : SELECT is_true_G_10.a_0 AS x, is_true_G_10.G AS G FROM is_true_G AS is_true_G_10
 - (exists ((x Bool)) (is_true x)):
    TU: SELECT or_aggregate(G) as G from (SELECT is_true_TU_10.a_0 AS x, "true" AS G FROM is_true_TU AS is_true_TU_10)
    UF: SELECT or_aggregate(G) as G from (SELECT is_true_G_10.a_0 AS x, is_true_G_10.G AS G FROM is_true_G AS is_true_G_10)
    G : SELECT or_aggregate(G) as G from (SELECT is_true_G_10.a_0 AS x, is_true_G_10.G AS G FROM is_true_G AS is_true_G_10)
 - (is_true (exists ((x Bool)) (is_true x))):
    T: SELECT "true" AS G FROM Agg_9_TU JOIN is_true_TU AS is_true_TU_12
    F: SELECT "false" AS G FROM Agg_9_UF JOIN is_true_UF AS is_true_UF_12
    G : SELECT is_true_G_12.G AS G FROM Agg_9_G JOIN is_true_G AS is_true_G_12
 - (not (is_true (exists ((x Bool)) (is_true x)))):
    T: SELECT "true" AS G FROM Agg_9_UF JOIN is_true_UF AS is_true_UF_12
    F: SELECT "false" AS G FROM Agg_9_TU JOIN is_true_TU AS is_true_TU_12
    G : SELECT not_(is_true_G_12.G) AS G FROM Agg_9_G JOIN is_true_G AS is_true_G_12
 TABLE: is_true_UF
┌─────────┬─────────┐
│ a_0     │ G       │
├─────────┼─────────┤
│ "false" │ "false" │
└─────────┴─────────┘
