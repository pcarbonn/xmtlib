(declare-datatype Color ( ( red ) ( green ) ))
(declare-datatype Pair (par (X) ((pair (first X) (second X)))))
(declare-fun bright (Color) Bool)
(declare-fun invert (Color) Color)
(declare-fun brightest ( (Pair Color) ) Color)
(x-debug solver sorts)
-------------------------
(declare-datatype Color ((red ) (green )))
(declare-datatype Pair (par (X) ((pair (first X) (second X)))))
(declare-fun bright (Color) Bool)
(declare-fun invert (Color) Color)
(declare-fun brightest ((Pair Color)) Color)
Sorts:
 - (Bool: 2) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (Color: 2) Color: ((red ) (green ))
 - (Sort_4: 4) (Pair Color): ((pair (first Color) (second Color)))