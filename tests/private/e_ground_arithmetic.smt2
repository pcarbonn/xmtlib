(set-option :backend none)
(assert (= 2 (+ 1 (abs 1))))
(assert (= 0 (- 3 1 2)))
(assert (= 4 (* 2 2 -1)))
(assert (= 1 (mod 3 2)))
(x-ground)
(x-debug solver groundings)
-------------------------





(assert (= 2 (+ 1 1)))
(assert (= 4 (* -1 4)))
(assert (= 1 (mod 3 2)))
Groundings:
 - 2: SELECT 2 AS G
 - 1: SELECT 1 AS G
 - (abs 1): SELECT abs_(1) AS G
 - (+ 1 (abs 1)): SELECT left_("+", 1, abs_(1)) AS G
 - (= 2 (+ 1 (abs 1))):
    T: SELECT eq_(2, left_("+", 1, abs_(1))) AS G
    F: SELECT eq_(2, left_("+", 1, abs_(1))) AS G
    G : SELECT eq_(2, left_("+", 1, abs_(1))) AS G
 - 0: SELECT 0 AS G
 - 3: SELECT 3 AS G
 - (- 3 1 2): SELECT left_("-", 3, 1, 2) AS G
 - (= 0 (- 3 1 2)):
    T: SELECT eq_(0, left_("-", 3, 1, 2)) AS G
    F: SELECT eq_(0, left_("-", 3, 1, 2)) AS G
    G : SELECT eq_(0, left_("-", 3, 1, 2)) AS G
 - 4: SELECT 4 AS G
 - -1: SELECT "-1" AS G
 - (* 2 2 -1): SELECT left_("*", 2, 2, "-1") AS G
 - (= 4 (* 2 2 -1)):
    T: SELECT eq_(4, left_("*", 2, 2, "-1")) AS G
    F: SELECT eq_(4, left_("*", 2, 2, "-1")) AS G
    G : SELECT eq_(4, left_("*", 2, 2, "-1")) AS G
 - (mod 3 2): SELECT apply("mod", 3, 2) AS G
 - (= 1 (mod 3 2)):
    T: SELECT eq_(1, apply("mod", 3, 2)) AS G
    F: SELECT eq_(1, apply("mod", 3, 2)) AS G
    G : SELECT eq_(1, apply("mod", 3, 2)) AS G