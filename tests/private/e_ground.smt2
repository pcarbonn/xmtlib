(set-option :backend none)
(assert false)
(assert (and true true))
(assert (or false false))


(declare-fun is_true (Bool) Bool)
(x-interpret-pred is_true (true))
(assert (is_true true))
(assert (not (is_true (exists ((x Bool)) (is_true x)))))

(x-ground)
(x-debug solver groundings)
(x-debug db is_true_UF)
-------------------------




(declare-fun is_true (Bool) Bool)
(x-interpret-pred is_true (true))


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
 - x: SELECT Bool_5.G AS x, Bool_5.G AS G FROM Bool AS Bool_5
 - (is_true x):
    T: SELECT is_true_TU_6.a_0 AS x, "true" AS G FROM is_true_TU AS is_true_TU_6
    F: SELECT is_true_UF_6.a_0 AS x, "false" AS G FROM is_true_UF AS is_true_UF_6
    G : SELECT is_true_G_6.a_0 AS x, is_true_G_6.G AS G FROM is_true_G AS is_true_G_6
 - (exists ((x Bool)) (is_true x)):
    TU: SELECT or_aggregate(G) as G from (SELECT is_true_TU_6.a_0 AS x, "true" AS G FROM is_true_TU AS is_true_TU_6)
    UF: SELECT or_aggregate(G) as G from (SELECT is_true_G_6.a_0 AS x, is_true_G_6.G AS G FROM is_true_G AS is_true_G_6)
    G : SELECT or_aggregate(G) as G from (SELECT is_true_G_6.a_0 AS x, is_true_G_6.G AS G FROM is_true_G AS is_true_G_6)
 - (is_true (exists ((x Bool)) (is_true x))):
    T: SELECT "true" AS G FROM Agg_5_TU JOIN is_true_TU AS is_true_TU_8
    F: SELECT "false" AS G FROM Agg_5_UF JOIN is_true_UF AS is_true_UF_8
    G : SELECT is_true_G_8.G AS G FROM Agg_5_G JOIN is_true_G AS is_true_G_8
 - (not (is_true (exists ((x Bool)) (is_true x)))):
    T: SELECT "true" AS G FROM Agg_5_UF JOIN is_true_UF AS is_true_UF_8
    F: SELECT "false" AS G FROM Agg_5_TU JOIN is_true_TU AS is_true_TU_8
    G : SELECT not_(is_true_G_8.G) AS G FROM Agg_5_G JOIN is_true_G AS is_true_G_8
 TABLE: is_true_UF
┌─────────┬─────────┐
│ a_0     │ G       │
├─────────┼─────────┤
│ "false" │ "false" │
└─────────┴─────────┘