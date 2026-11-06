import Mathlib

theorem algebra_22192 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : Real.log x - Real.log y = a) (h2 : Real.log y - Real.log z = 15) (h3 : Real.log z - Real.log x = -7) :
    a = -8 := by
  linarith