(set-option :backend none)
; arity 0
(declare-fun p () Bool)
(x-interpret-pred p )
(assert p)

; arity 1
(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun bright (Color) Bool)
(x-interpret-pred bright (red))
(assert (exists ((x Color)) (bright x) ))

; arity 2
(declare-fun same (Color Color) Bool)
(x-interpret-pred same (red red) (green green))
(assert (exists ((x Color)) (same x x) ))
(x-ground)
(x-debug db bright_TU)
(x-debug db bright_G)
(x-debug db-view Agg_1_UF)
(x-debug solver functions)
(x-debug solver groundings)
-------------------------

(declare-fun p () Bool)
(x-interpret-pred p )

(declare-datatype Color ((red ) (green )))
(declare-fun bright (Color) Bool)
(x-interpret-pred bright (red))

(declare-fun same (Color Color) Bool)
(x-interpret-pred same (red red) (green green))

(push)
(assert p)
(pop)
(assert false)
(push)
(assert (exists ((x Color)) (bright x)))
(pop)
(push)
(assert (exists ((x Color)) (same x x)))
(pop)
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
CREATE VIEW Agg_1_UF AS SELECT or_aggregate(G) as G from (SELECT bright_G_2.a_0 AS x, bright_G_2.G AS G FROM bright_G AS bright_G_2) HAVING or_aggregate(G) <> "true"
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
 - p: Boolean (p_TU Complete, p_UF Complete, p_G Complete)
 - bright: Boolean (bright_TU Complete, bright_UF Complete, bright_G Complete)
 - same: Boolean (same_TU Complete, same_UF Complete, same_G Complete)
Groundings:
 - p:
    T: SELECT "true" AS G FROM p_TU AS p_TU
    F: SELECT "false" AS G FROM p_UF AS p_UF
    G : SELECT p_G.G AS G FROM p_G AS p_G
 - x: SELECT Color_1.G AS x, Color_1.G AS G FROM Color AS Color_1
 - (bright x):
    T: SELECT bright_TU_2.a_0 AS x, "true" AS G FROM bright_TU AS bright_TU_2
    F: SELECT bright_UF_2.a_0 AS x, "false" AS G FROM bright_UF AS bright_UF_2
    G : SELECT bright_G_2.a_0 AS x, bright_G_2.G AS G FROM bright_G AS bright_G_2
 - (exists ((x Color)) (bright x)):
    TU: SELECT or_aggregate(G) as G from (SELECT bright_TU_2.a_0 AS x, "true" AS G FROM bright_TU AS bright_TU_2)
    UF: SELECT or_aggregate(G) as G from (SELECT bright_G_2.a_0 AS x, bright_G_2.G AS G FROM bright_G AS bright_G_2) HAVING or_aggregate(G) <> "true"
    G : SELECT or_aggregate(G) as G from (SELECT bright_G_2.a_0 AS x, bright_G_2.G AS G FROM bright_G AS bright_G_2)
 - (same x x):
    T: SELECT same_TU_4.a_1 AS x, "true" AS G FROM same_TU AS same_TU_4 WHERE same_TU_4.a_1 = same_TU_4.a_0
    F: SELECT same_UF_4.a_1 AS x, "false" AS G FROM same_UF AS same_UF_4 WHERE same_UF_4.a_1 = same_UF_4.a_0
    G : SELECT same_G_4.a_1 AS x, same_G_4.G AS G FROM same_G AS same_G_4 WHERE same_G_4.a_1 = same_G_4.a_0
 - (exists ((x Color)) (same x x)):
    TU: SELECT or_aggregate(G) as G from (SELECT same_TU_4.a_1 AS x, "true" AS G FROM same_TU AS same_TU_4 WHERE same_TU_4.a_1 = same_TU_4.a_0)
    UF: SELECT or_aggregate(G) as G from (SELECT same_G_4.a_1 AS x, same_G_4.G AS G FROM same_G AS same_G_4 WHERE same_G_4.a_1 = same_G_4.a_0) HAVING or_aggregate(G) <> "true"
    G : SELECT or_aggregate(G) as G from (SELECT same_G_4.a_1 AS x, same_G_4.G AS G FROM same_G AS same_G_4 WHERE same_G_4.a_1 = same_G_4.a_0)