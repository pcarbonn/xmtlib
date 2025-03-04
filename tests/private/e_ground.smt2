(set-option :backend none)
(assert false)
(assert (and true true))
(assert (or false false))


(declare-fun is_true (Bool) Bool)
(x-interpret-pred is_true (true))

(assert (not (is_true (exists ((x Bool)) (is_true x)))))

(x-ground)
(x-debug solver groundings)
(x-debug db is_true_UF)
-------------------------




(declare-fun is_true (Bool) Bool)
(x-interpret-pred is_true (true))

(push)
(assert false)
(pop)
(assert false)
(push)
(assert (and true true))
(pop)
(push)
(assert (or false false))
(pop)
(assert false)
(push)
(assert (not (is_true (exists ((x Bool)) (is_true x)))))
(pop)
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
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT "false" AS G
 - x: SELECT Bool_4.G AS x, Bool_4.G AS G FROM Bool AS Bool_4
 - (is_true x):
    T: SELECT is_true_TU_5.a_0 AS x, "true" AS G FROM is_true_TU AS is_true_TU_5
    F: SELECT is_true_UF_5.a_0 AS x, "false" AS G FROM is_true_UF AS is_true_UF_5
    G : SELECT is_true_G_5.a_0 AS x, is_true_G_5.G AS G FROM is_true_G AS is_true_G_5
 - (exists ((x Bool)) (is_true x)):
    TU: SELECT or_aggregate(G) as G from (SELECT is_true_TU_5.a_0 AS x, "true" AS G FROM is_true_TU AS is_true_TU_5)
    UF: SELECT or_aggregate(G) as G from (SELECT is_true_G_5.a_0 AS x, is_true_G_5.G AS G FROM is_true_G AS is_true_G_5) HAVING or_aggregate(G) <> "true"
    G : SELECT or_aggregate(G) as G from (SELECT is_true_G_5.a_0 AS x, is_true_G_5.G AS G FROM is_true_G AS is_true_G_5)
 - (is_true (exists ((x Bool)) (is_true x))):
    T: SELECT "true" AS G FROM Agg_4_TU JOIN is_true_TU AS is_true_TU_7
    F: SELECT "false" AS G FROM Agg_4_UF JOIN is_true_UF AS is_true_UF_7
    G : SELECT is_true_G_7.G AS G FROM Agg_4_G JOIN is_true_G AS is_true_G_7
 - (not (is_true (exists ((x Bool)) (is_true x)))):
    T: SELECT "true" AS G FROM Agg_4_UF JOIN is_true_UF AS is_true_UF_7
    F: SELECT "false" AS G FROM Agg_4_TU JOIN is_true_TU AS is_true_TU_7
    G : SELECT not_(is_true_G_7.G) AS G FROM Agg_4_G JOIN is_true_G AS is_true_G_7
 TABLE: is_true_UF
┌─────────┬─────────┐
│ a_0     │ G       │
├─────────┼─────────┤
│ "false" │ "false" │
└─────────┴─────────┘