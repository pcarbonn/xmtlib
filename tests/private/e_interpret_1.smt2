(set-option :backend none)
; arity 1
(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun bright (Color) Bool)
(x-interpret-pred bright (red))
(x-debug db bright_TU)
(x-debug db bright_G)
(x-debug solver functions)
(assert (exists ((x Color)) (bright x) ))
; arity 2
(declare-fun same (Color Color) Bool)
(x-interpret-pred same (red red) (green green))
(assert (exists ((x Color)) (same x x) ))
(x-ground)
(x-debug db-view Agg_0_UF)
(x-debug solver groundings)
-------------------------

(declare-datatype Color ((red ) (green )))
(declare-fun bright (Color) Bool)
(x-interpret-pred bright (red))
 TABLE: bright_TU
┌───────┬────────┐
│ a_0   │ G      │
├───────┼────────┤
│ "red" │ "true" │
└───────┴────────┘
 TABLE: bright_G
┌─────────┬─────────┐
│ a_0     │ G       │
├─────────┼─────────┤
│ "green" │ "false" │
├─────────┼─────────┤
│ "red"   │ "true"  │
└─────────┴─────────┘
Functions:
 - true: (boolean) (calculated)
 - false: (boolean) (calculated)
 - not: (boolean) (calculated)
 - =>: (boolean) (calculated)
 - and: (boolean) (calculated)
 - or: (boolean) (calculated)
 - xor: (boolean) (calculated)
 - =: (boolean) (calculated)
 - distinct: (boolean) (calculated)
 - <=: (boolean) (calculated)
 - <: (boolean) (calculated)
 - >=: (boolean) (calculated)
 - >: (boolean) (calculated)
 - ite: (boolean ?) (calculated)
 - +: (non-boolean) (calculated)
 - -: (non-boolean) (calculated)
 - *: (non-boolean) (calculated)
 - div: (non-boolean) (calculated)
 - mod: (non-boolean) (calculated)
 - abs: (non-boolean) (calculated)
 - bright: Color -> Bool (bright_G Complete)

(declare-fun same (Color Color) Bool)
(x-interpret-pred same (red red) (green green))

(push)
(assert (exists ((x Color)) (bright x)))
(pop)
(assert true)
(push)
(assert (exists ((x Color)) (same x x)))
(pop)
(assert true)
CREATE VIEW Agg_0_UF AS SELECT or_aggregate(G) as G from (SELECT bright_G.a_0 AS x, bright_G.G AS G FROM bright_G AS bright_G) HAVING or_aggregate(G) <> true
Groundings:
 - x: SELECT Color.G AS x, Color.G AS G FROM Color
 - (bright x):
    TU: SELECT bright_TU.a_0 AS x, bright_TU.G AS G FROM bright_TU AS bright_TU
    UF: SELECT bright_UF.a_0 AS x, bright_UF.G AS G FROM bright_UF AS bright_UF
    G : SELECT bright_G.a_0 AS x, bright_G.G AS G FROM bright_G AS bright_G
 - (exists () (bright x)):
    TU: SELECT Agg_0_TU.G AS G FROM Agg_0_TU
    UF: SELECT Agg_0_UF.G AS G FROM Agg_0_UF
    G : SELECT Agg_0_G.G AS G FROM Agg_0_G
 - (same x x):
    TU: SELECT same_TU_3.a_1 AS x, same_TU_3.G AS G FROM same_TU AS same_TU_3 WHERE same_TU_3.a_1 = same_TU_3.a_0
    UF: SELECT same_UF_3.a_1 AS x, same_UF_3.G AS G FROM same_UF AS same_UF_3 WHERE same_UF_3.a_1 = same_UF_3.a_0
    G : SELECT same_G_3.a_1 AS x, same_G_3.G AS G FROM same_G AS same_G_3 WHERE same_G_3.a_1 = same_G_3.a_0
 - (exists () (same x x)):
    TU: SELECT Agg_3_TU.G AS G FROM Agg_3_TU
    UF: SELECT Agg_3_UF.G AS G FROM Agg_3_UF
    G : SELECT Agg_3_G.G AS G FROM Agg_3_G