(set-option :backend none)
(declare-datatypes ( (Tree 1) (TreeList 1) ) (
    ; tree
        ( par ( X ) ( ( node ( value X ) ( children ( TreeList X )) )))
    ; TreeList
        ( par ( Y ) ( ( empty )
                      ( insert ( head ( Tree Y )) ( tail ( TreeList Y ))) ))
    )
)
(declare-datatype TreeInt ( (treeint (value (Tree Int)))))
; declare-sort
(declare-sort Pair 2)
(declare-sort A 0)
(declare-sort B 0)
(define-sort MyPair () (Pair A B))
(x-debug solver parametric_sorts)
(x-debug solver sorts)
(x_debug db TreeInt)
(check-sat)
-------------------------

(declare-datatypes ((Tree 1) (TreeList 1)) ((par (X) ((node (value X) (children (TreeList X))))) (par (Y) ((empty ) (insert (head (Tree Y)) (tail (TreeList Y)))))))
(declare-datatype TreeInt ((treeint (value (Tree Int)))))
(declare-sort Pair 2)
(declare-sort A 0)
(declare-sort B 0)
(define-sort MyPair () (Pair A B))
Parametric datatypes:
 - (unknown): Array
 - (recursive): Tree
 - (recursive): TreeList
 - (unknown): Pair
Sorts:
 - (Bool: 2) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (infinite) RoundingMode
 - (infinite) String
 - (infinite) RegLan
 - (recursive) (Tree Int)
 - (recursive) TreeInt
 - (unknown) A
 - (unknown) B
 - (unknown) (Pair A B)
 - (unknown) MyPair
(check-sat)