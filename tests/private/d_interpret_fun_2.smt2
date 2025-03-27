(set-option :backend none)
; arity 2
(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun mix (Color Color) Color)
(x-interpret-fun mix
   ( ((red red) red)
     ((green green) green)
   )
   red)

(x-ground)
(x-debug solver functions)
(x-debug solver groundings)
-------------------------

(declare-datatype Color ((red ) (green )))
(declare-fun mix (Color Color) Color)
(x-interpret-fun mix ( ((red red) red) ((green green) green) ) red)
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
 - mix: Color * Color -> Color (false)
Groundings: