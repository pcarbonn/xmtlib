(declare-datatype Color ( ( red ) ( green ) ))
(declare-fun bright (Color) Bool)
(x-interpret-pred bright (red))

-------------------------
(declare-datatype Color ((red ) (green )))
(declare-fun bright (Color) Bool)
(x-interpret-pred bright (red))