(set-option :backend none)
(declare-datatype Color ( ( red ) ( green ) ))
(declare-datatype Pair (par (X) ((pair (first X) (second X)))))
(declare-fun bright (Color) Bool)
(declare-fun invert (Color) Color)
(declare-fun brightest ( (Pair Color) ) Color)
(declare-fun colorOf ( Int ) Color)
(x-debug solver sorts)
(x-debug solver functions)
-------------------------

(declare-datatype Color ((red ) (green )))
(declare-datatype Pair (par (X) ((pair (first X) (second X)))))
(declare-fun bright (Color) Bool)
(declare-fun invert (Color) Color)
(declare-fun brightest ((Pair Color)) Color)
(declare-fun colorOf (Int) Color)
Sorts:
 - (Bool: 2) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (infinite) RoundingMode
 - (infinite) String
 - (infinite) RegLan
 - (Color: 2) Color: ((red ) (green ))
 - (Sort_7: 4) (Pair Color): ((pair (first Color) (second Color)))
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
 - bright: Color -> Bool (true)
 - invert: Color -> Color (false)
 - brightest: (Pair Color) -> Color (false)
 - colorOf: Int -> Color (false)