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
 - true:  -> Bool (calculated)
 - false:  -> Bool (calculated)
 - not: Bool -> Bool (calculated)
 - =>: Bool * Bool -> Bool (calculated)
 - and: Bool * Bool -> Bool (calculated)
 - or: Bool * Bool -> Bool (calculated)
 - xor: Bool * Bool -> Bool (calculated)
 - bright: Color -> Bool (calculated)
 - invert: Color -> Color (calculated)
 - brightest: (Pair Color) -> Color (calculated)
 - colorOf: Int -> Color (calculated)