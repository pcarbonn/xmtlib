(set-option :backend none)
(assert (<= 2 2 2))
(assert (< 1 2 3))
(assert (not (= 2 2)))
(assert (= (<= 2 2) (not (<= 3 3))))
(assert (and (<= 2 2) (not (<= 3 3))))
(x-ground)
(x-debug solver groundings)
-------------------------






(assert false)
(assert false)
(assert false)
Groundings:
 - 2: SELECT 2 AS G
 - (<= 2 2 2):
    T: SELECT compare_("<=", 2, 2, 2) AS G
    F: SELECT compare_("<=", 2, 2, 2) AS G
    G : SELECT compare_("<=", 2, 2, 2) AS G
 - 1: SELECT 1 AS G
 - 3: SELECT 3 AS G
 - (< 1 2 3):
    T: SELECT compare_("<", 1, 2, 3) AS G
    F: SELECT compare_("<", 1, 2, 3) AS G
    G : SELECT compare_("<", 1, 2, 3) AS G
 - (= 2 2):
    T: SELECT "true" AS G
    F: SELECT "true" AS G
    G : SELECT "true" AS G
 - (not (= 2 2)):
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT not_("true") AS G
 - (<= 2 2):
    T: SELECT compare_("<=", 2, 2) AS G
    F: SELECT compare_("<=", 2, 2) AS G
    G : SELECT compare_("<=", 2, 2) AS G
 - (<= 3 3):
    T: SELECT compare_("<=", 3, 3) AS G
    F: SELECT compare_("<=", 3, 3) AS G
    G : SELECT compare_("<=", 3, 3) AS G
 - (not (<= 3 3)):
    T: SELECT "true" AS G
    F: SELECT "false" AS G
    G : SELECT not_(compare_("<=", 3, 3)) AS G
 - (= (<= 2 2) (not (<= 3 3))):
    T: SELECT eq_(compare_("<=", 2, 2), not_(compare_("<=", 3, 3))) AS G
    F: SELECT eq_(compare_("<=", 2, 2), not_(compare_("<=", 3, 3))) AS G
    G : SELECT eq_(compare_("<=", 2, 2), not_(compare_("<=", 3, 3))) AS G
 - (and (<= 2 2) (not (<= 3 3))):
    T: SELECT compare_("<=", 2, 2) AS G
    UF: SELECT and_aggregate(G) as G from (SELECT compare_("<=", 2, 2) AS G UNION SELECT "false" AS G)
    G : SELECT and_(compare_("<=", 2, 2), not_(compare_("<=", 3, 3))) AS G