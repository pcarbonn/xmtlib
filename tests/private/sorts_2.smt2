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
(check-sat)
-------------------------
(declare-datatypes ((Tree 1) (TreeList 1)) ((par (X) ((node (value X) (children (TreeList X))))) (par (Y) ((empty ) (insert (head (Tree Y)) (tail (TreeList Y)))))))
(declare-datatype TreeInt ((treeint (value (Tree Int)))))
(declare-sort Pair 2)
(declare-sort A 0)
(declare-sort B 0)
(define-sort MyPair () (Pair A B))
Parametric datatypes:
 - (recursive): Tree
 - (recursive): TreeList
 - (unknown): Pair
Sorts:
 - (Bool: 2) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (recursive) (Tree Int)
 - (recursive) TreeInt
 - (unknown) A
 - (unknown) B
 - (unknown) (Pair A B)
 - (unknown) MyPair
sat