(set-option :backend none)
(declare-datatype Color ( ( red ) ( green ) ))
(declare-datatype Hue ( ( hue (first Color) (second Color) ) ))
(declare-fun dim (Hue) Bool)
(x-interpret-pred dim ((hue red red)))
(assert (exists ((x Hue)) (dim x) ))

(x-ground)
(x-debug db Color)
(x-debug db Hue)
(x-debug db dim_T)
(x-debug solver functions)
(x-debug solver groundings)
-------------------------
(declare-datatype Color ((red ) (green )))
(declare-datatype Hue ((hue (first Color) (second Color))))
(declare-fun dim (Hue) Bool)
 TABLE: Color
┌─────────┐
│ G       │
├─────────┤
│ "red"   │
├─────────┤
│ "green" │
└─────────┘
 TABLE: Hue
┌─────────────┬─────────┬─────────┬──────────────────────┐
│ constructor │ first   │ second  │ G                    │
├─────────────┼─────────┼─────────┼──────────────────────┤
│ "hue"       │ "red"   │ "red"   │ " (hue red red)"     │
├─────────────┼─────────┼─────────┼──────────────────────┤
│ "hue"       │ "red"   │ "green" │ " (hue red green)"   │
├─────────────┼─────────┼─────────┼──────────────────────┤
│ "hue"       │ "green" │ "red"   │ " (hue green red)"   │
├─────────────┼─────────┼─────────┼──────────────────────┤
│ "hue"       │ "green" │ "green" │ " (hue green green)" │
└─────────────┴─────────┴─────────┴──────────────────────┘
 TABLE: dim_T
┌──────────────────┐
│ a_0              │
├──────────────────┤
│ " (hue red red)" │
└──────────────────┘
Functions:
 - true: Constructor
 - false: Constructor
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
 - red: Constructor
 - green: Constructor
 - hue: Constructor
 - dim: Boolean (dim_TU Complete, dim_UF Complete, dim_G Complete)
Groundings:
 - x: SELECT Hue.G AS x, Hue.G AS G FROM Hue
 - (dim x):
    T: SELECT dim_TU_1.a_0 AS x, "true" AS G FROM dim_TU AS dim_TU_1
    F: SELECT dim_UF_1.a_0 AS x, "false" AS G FROM dim_UF AS dim_UF_1
    G : SELECT dim_G_1.a_0 AS x, dim_G_1.G AS G FROM dim_G AS dim_G_1
 - (exists ((x Hue)) (dim x)):
    TU: SELECT or_aggregate(G) as G from (SELECT dim_TU_1.a_0 AS x, "true" AS G FROM dim_TU AS dim_TU_1)
    UF: SELECT or_aggregate(G) as G from (SELECT dim_G_1.a_0 AS x, dim_G_1.G AS G FROM dim_G AS dim_G_1)
    G : SELECT or_aggregate(G) as G from (SELECT dim_G_1.a_0 AS x, dim_G_1.G AS G FROM dim_G AS dim_G_1)
