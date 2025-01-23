(declare-datatypes ( (Tree 1) (TreeList 1) ) (
    ; tree
        ( par ( X ) ( ( node ( value X ) ( children ( TreeList X )) )))
    ; TreeList
        ( par ( Y ) ( ( empty )
                      ( insert ( head ( Tree Y )) ( tail ( TreeList Y ))) ))
    )
)
(declare-datatype TreeInt ( (treeint (value (Tree Int)))))
(x-debug parametric_datatypes)
(x-debug sorts)
(check-sat)
-------------------------
(declare-datatypes ((Tree 1) (TreeList 1)) ((par (X) ((node (value X) (children (TreeList X))))) (par (Y) ((empty ) (insert (head (Tree Y)) (tail (TreeList Y)))))))
(declare-datatype TreeInt ((treeint (value (Tree Int)))))
Parametric datatypes:
 - (recursive): Tree
 - (recursive): TreeList
Sorts:
 - (Bool) Bool: ((true ) (false ))
 - (infinite) Int
 - (infinite) Real
 - (recursive) (Tree Int)
 - (recursive) TreeInt
sat