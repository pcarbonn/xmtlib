(declare-datatype Color ( ( red ) ( green ) ( blue ) ))
(declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))
(declare-datatype P ( (p (x (Pair Color Color)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X (Pair X X)))))))
(declare-datatype Q ( (q (x (Triplet Color)))))
(declare-datatype R ( (r (x Int))))
(declare-datatype ColorList ( (nil) (cons (head Color) (tail ColorList))))
(x-debug parametric_datatypes)
(x-debug sorts)
(check-sat)
-------------------------
(declare-datatype Color ((red ) (green ) (blue )))
(declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))
(declare-datatype P ((p (x (Pair Color Color)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X (Pair X X)))))))
(declare-datatype Q ((q (x (Triplet Color)))))
(declare-datatype R ((r (x Int))))
(declare-datatype ColorList ((nil ) (cons (head Color) (tail ColorList))))
Parametric datatypes:
 - Pair: (par (X Y) ((pair (first X) (second Y))))
 - Triplet: (par (X) ((triplet (first (Pair X (Pair X X))))))
Sorts:
 - Bool: ((true ) (false )) (Bool)
 - Int: infinite
 - Real: infinite
 - Color: ((red ) (green ) (blue )) (Sort_3)
 - (Pair Color Color): ((pair (first Color) (second Color))) (Sort_4)
 - P: ((p (x (Pair Color Color)))) (Sort_5)
 - (Pair Color (Pair Color Color)): ((pair (first Color) (second (Pair Color Color)))) (Sort_6)
 - (Triplet Color): ((triplet (first (Pair Color (Pair Color Color))))) (Sort_7)
 - Q: ((q (x (Triplet Color)))) (Sort_8)
 - R: ((r (x Int))) (infinite)
 - ColorList: ((nil ) (cons (head Color) (tail ColorList))) (infinite)
sat