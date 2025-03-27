(set-option :backend none)
; arity 2
(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun mix (Color Color) Color)
(x-interpret-fun mix
   ( ((red red) green)
     ((green green) red)
     ((red green) green)
     ((green red) green)
   )
   red)
(assert (exists ((x Color)) (= (mix x x) x)))
(x-ground)
(x-debug solver functions)
(x-debug solver groundings)
(x-debug db mix_g)
-------------------------

(declare-datatype Color ((red ) (green )))
(declare-fun mix (Color Color) Color)
(x-interpret-fun mix ( ((red red) green) ((green green) red) ((red green) green) ((green red) green) ) red)

(push)
(assert (exists ((x Color)) (= (mix x x) x)))
(pop)
(assert false)
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
 - mix: Non Boolean (mix_G Complete)
Groundings:
 - x: SELECT Color.G AS x, Color.G AS G FROM Color
 - (mix x x): SELECT mix_G_1.a_1 AS x, mix_G_1.G AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0
 - (= (mix x x) x):
    T: SELECT mix_G_1.a_1 AS x, eq_(mix_G_1.G, mix_G_1.a_1) AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0
    F: SELECT mix_G_1.a_1 AS x, eq_(mix_G_1.G, mix_G_1.a_1) AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0
    G : SELECT mix_G_1.a_1 AS x, eq_(mix_G_1.G, mix_G_1.a_1) AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0
 - (exists ((x Color)) (= (mix x x) x)):
    TU: SELECT or_aggregate(G) as G from (SELECT mix_G_1.a_1 AS x, eq_(mix_G_1.G, mix_G_1.a_1) AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0)
    UF: SELECT or_aggregate(G) as G from (SELECT mix_G_1.a_1 AS x, eq_(mix_G_1.G, mix_G_1.a_1) AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0)
    G : SELECT or_aggregate(G) as G from (SELECT mix_G_1.a_1 AS x, eq_(mix_G_1.G, mix_G_1.a_1) AS G FROM mix_G AS mix_G_1 WHERE mix_G_1.a_1 = mix_G_1.a_0)
 TABLE: mix_g
┌─────────┬─────────┬─────────┐
│ a_0     │ a_1     │ G       │
├─────────┼─────────┼─────────┤
│ "red"   │ "red"   │ "green" │
├─────────┼─────────┼─────────┤
│ "green" │ "green" │ "red"   │
├─────────┼─────────┼─────────┤
│ "red"   │ "green" │ "green" │
├─────────┼─────────┼─────────┤
│ "green" │ "red"   │ "green" │
└─────────┴─────────┴─────────┘