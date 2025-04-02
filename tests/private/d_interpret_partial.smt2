(set-option :backend none)
; arity 2
(declare-datatype Color ( ( red ) ( green ) ))

; arity 2
(declare-fun mix (Color Color) Color)
(x-interpret-fun mix
   (
     ((green green) red)
     ((red green) green)
     ((green red) green)
   )
   ? )
(assert (= green (mix red green)))
(assert (exists ((x Color)) (= (mix x x) x)))
(x-ground)
(x-debug solver functions)
(x-debug solver groundings)
(x-debug db mix_g)
-------------------------

(declare-datatype Color ((red ) (green )))
(declare-fun mix (Color Color) Color)
(x-interpret-fun mix ( ((green green) red) ((red green) green) ((green red) green) ) ?)


(assert (= (mix red red) red))
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
 - mix: Non Boolean (mix_G?? Complete)
Groundings:
 - green: SELECT "green" AS G
 - red: SELECT "red" AS G
 - (mix red green): SELECT IFNULL(mix_G_2.G, apply("mix", "red", "green")) AS G FROM mix_G AS mix_G_2 WHERE "red" = mix_G_2.a_0 AND "green" = mix_G_2.a_1
 - (= green (mix red green)):
    T: SELECT eq_("green", IFNULL(mix_G_2.G, apply("mix", "red", "green"))) AS G FROM mix_G AS mix_G_2 WHERE "red" = mix_G_2.a_0 AND "green" = mix_G_2.a_1
    F: SELECT eq_("green", IFNULL(mix_G_2.G, apply("mix", "red", "green"))) AS G FROM mix_G AS mix_G_2 WHERE "red" = mix_G_2.a_0 AND "green" = mix_G_2.a_1
    G : SELECT eq_("green", IFNULL(mix_G_2.G, apply("mix", "red", "green"))) AS G FROM mix_G AS mix_G_2 WHERE "red" = mix_G_2.a_0 AND "green" = mix_G_2.a_1
 - x: SELECT Color_4.G AS x, Color_4.G AS G FROM Color AS Color_4
 - (mix x x): SELECT Color_4.G AS x, IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1
 - (= (mix x x) x):
    T: SELECT Color_4.G AS x, eq_(IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)), Color_4.G) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1
    F: SELECT Color_4.G AS x, eq_(IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)), Color_4.G) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1
    G : SELECT Color_4.G AS x, eq_(IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)), Color_4.G) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1
 - (exists ((x Color)) (= (mix x x) x)):
    TU: SELECT or_aggregate(G) as G from (SELECT Color_4.G AS x, eq_(IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)), Color_4.G) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1)
    UF: SELECT or_aggregate(G) as G from (SELECT Color_4.G AS x, eq_(IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)), Color_4.G) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1)
    G : SELECT or_aggregate(G) as G from (SELECT Color_4.G AS x, eq_(IFNULL(mix_G_5.G, apply("mix", Color_4.G, Color_4.G)), Color_4.G) AS G FROM Color AS Color_4 LEFT JOIN mix_G AS mix_G_5 ON Color_4.G = mix_G_5.a_0 AND Color_4.G = mix_G_5.a_1)
 TABLE: mix_g
┌─────────┬─────────┬─────────┐
│ a_0     │ a_1     │ G       │
├─────────┼─────────┼─────────┤
│ "green" │ "green" │ "red"   │
├─────────┼─────────┼─────────┤
│ "red"   │ "green" │ "green" │
├─────────┼─────────┼─────────┤
│ "green" │ "red"   │ "green" │
└─────────┴─────────┴─────────┘