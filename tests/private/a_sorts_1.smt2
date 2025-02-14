; declare-datatype
(set-option :backend none)
(declare-datatype Color ( ( red ) ( green ) ))
(declare-datatype Pair (par (X Y) ( ( white ) (pair (first X) (second Y)))))
(declare-datatype P ( (p (x (Pair Color Color)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X (Pair X X)))))))
(declare-datatype Q ( (q (x (Triplet Color)))))
(declare-datatype R ( (r (x Int))))
(declare-datatype ColorList ( (nil) (cons (head Color) (tail (Triplet ColorList)))))
(define-sort MyPair (T) (Pair T T))
(define-sort PairColor () (Pair Color Color))
(define-sort MyPairColor () (MyPair Color))
(define-sort MyBitVec () (MyPair (_ BitVec 2)))
(define-sort MyArray () (Array Color Color))
(x-debug solver parametric_sorts)
(x-debug solver sorts)
(x-debug db Q)
(check-sat)
-------------------------

(declare-datatype Color ((red ) (green )))
(declare-datatype Pair (par (X Y) ((white ) (pair (first X) (second Y)))))
(declare-datatype P ((p (x (Pair Color Color)))))
(declare-datatype Triplet (par (X) ((triplet (first (Pair X (Pair X X)))))))
(declare-datatype Q ((q (x (Triplet Color)))))
(declare-datatype R ((r (x Int))))
(declare-datatype ColorList ((nil ) (cons (head Color) (tail (Triplet ColorList)))))
(define-sort MyPair (T) (Pair T T))
(define-sort PairColor () (Pair Color Color))
(define-sort MyPairColor () (MyPair Color))
(define-sort MyBitVec () (MyPair (_ BitVec 2)))
(define-sort MyArray () (Array Color Color))
Parametric datatypes:
 - (unknown): Array
 - Pair: (par (X Y) ((white ) (pair (first X) (second Y))))
 - Triplet: (par (X) ((triplet (first (Pair X (Pair X X))))))
 - MyPair: (T) -> (Pair T T)
Sorts:
 - (Bool: 2) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (infinite) RoundingMode
 - (infinite) String
 - (infinite) RegLan
 - (Color: 2) Color: ((red ) (green ))
 - (Sort_7: 5) (Pair Color Color): ((white ) (pair (first Color) (second Color)))
 - (P: 5) P: ((p (x (Pair Color Color))))
 - (Sort_9: 11) (Pair Color (Pair Color Color)): ((white ) (pair (first Color) (second (Pair Color Color))))
 - (Sort_10: 11) (Triplet Color): ((triplet (first (Pair Color (Pair Color Color)))))
 - (Q: 11) Q: ((q (x (Triplet Color))))
 - (infinite) R
 - (recursive) ColorList
 - (recursive) (Pair ColorList ColorList)
 - (recursive) (Pair ColorList (Pair ColorList ColorList))
 - (recursive) (Triplet ColorList)
 - ( Sort_7: 5) PairColor: ((white ) (pair (first Color) (second Color)))
 - (unknown) (MyPair Color)
 - (unknown) MyPairColor
 - (unknown) (_ BitVec 2)
 - (unknown) (Pair (_ BitVec 2) (_ BitVec 2))
 - (unknown) (MyPair (_ BitVec 2))
 - (unknown) MyBitVec
 - (unknown) (Array Color Color)
 - (unknown) MyArray
 TABLE: Q
┌─────────────┬────────────────────────────────────────────────┬─────────────────────────────────────────────────────┐
│ constructor │ x                                              │ G                                                   │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet white)"                             │ " (q  (triplet white))"                             │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair green  (pair green green)))" │ " (q  (triplet  (pair green  (pair green green))))" │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair green  (pair green red)))"   │ " (q  (triplet  (pair green  (pair green red))))"   │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair green  (pair red green)))"   │ " (q  (triplet  (pair green  (pair red green))))"   │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair green  (pair red red)))"     │ " (q  (triplet  (pair green  (pair red red))))"     │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair green white))"               │ " (q  (triplet  (pair green white)))"               │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair red  (pair green green)))"   │ " (q  (triplet  (pair red  (pair green green))))"   │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair red  (pair green red)))"     │ " (q  (triplet  (pair red  (pair green red))))"     │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair red  (pair red green)))"     │ " (q  (triplet  (pair red  (pair red green))))"     │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair red  (pair red red)))"       │ " (q  (triplet  (pair red  (pair red red))))"       │
├─────────────┼────────────────────────────────────────────────┼─────────────────────────────────────────────────────┤
│ "q"         │ " (triplet  (pair red white))"                 │ " (q  (triplet  (pair red white)))"                 │
└─────────────┴────────────────────────────────────────────────┴─────────────────────────────────────────────────────┘
(check-sat)