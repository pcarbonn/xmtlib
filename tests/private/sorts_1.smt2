; declare-datatype
(declare-datatype Color ( ( red ) ( green ) ( blue ) ))
(declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))
(declare-datatype P ( (p (x (Pair Color Color)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X (Pair X X)))))))
(declare-datatype Q ( (q (x (Triplet Color)))))
(declare-datatype R ( (r (x Int))))
(declare-datatype ColorList ( (nil) (cons (head Color) (tail (Triplet ColorList)))))
;(define-sort MyPair (T) (Pair T T))
(define-sort MyPairColor () (Pair Color Color))
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
(declare-datatype ColorList ((nil ) (cons (head Color) (tail (Triplet ColorList)))))
(define-sort MyPairColor () (Pair Color Color))
Parametric datatypes:
 - Pair: (par (X Y) ((pair (first X) (second Y))))
 - Triplet: (par (X) ((triplet (first (Pair X (Pair X X))))))
Sorts:
 - (Bool) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (Color) Color: ((red ) (green ) (blue ))
 - (Sort_4) (Pair Color Color): ((pair (first Color) (second Color)))
 - (P) P: ((p (x (Pair Color Color))))
 - (Sort_6) (Pair Color (Pair Color Color)): ((pair (first Color) (second (Pair Color Color))))
 - (Sort_7) (Triplet Color): ((triplet (first (Pair Color (Pair Color Color)))))
 - (Q) Q: ((q (x (Triplet Color))))
 - (infinite) R
 - (recursive) ColorList
 - (recursive) (Pair ColorList ColorList)
 - (recursive) (Pair ColorList (Pair ColorList ColorList))
 - (recursive) (Triplet ColorList)
 - (Sort_4) MyPairColor: ((pair (first Color) (second Color)))
sat