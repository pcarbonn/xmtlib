(declare-datatype Color ( ( red ) ( green ) ( blue ) ))
(declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X X)) (second X)))))
(declare-datatype P ( (p (x (Pair Color Color)))))
(declare-datatype Q ( (q (x (Triplet Color)))))
(x-debug parametric_datatypes)
(x-debug sorts)
(check-sat)
-------------------------
(declare-datatype Color ((red ) (green ) (blue )))
(declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X X)) (second X)))))
(declare-datatype P ((p (x (Pair Color Color)))))
(declare-datatype Q ((q (x (Triplet Color)))))
Parametric datatypes:
 - Pair: (par (X Y) ((pair (first X) (second Y))))
 - Triplet: (par (X) ((triplet (first (Pair X X)) (second X))))
Sorts:
 - Color: ((red ) (green ) (blue ))
 - (Pair Color Color): ((pair (first Color) (second Color)))
 - P: ((p (x (Pair Color Color))))
 - (Triplet Color): ((triplet (first (Pair Color Color)) (second Color)))
 - Q: ((q (x (Triplet Color))))
sat