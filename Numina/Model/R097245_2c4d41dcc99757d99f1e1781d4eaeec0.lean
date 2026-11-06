import Mathlib

theorem algebra_267143 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 8 = b * 6) (h2 : 0 < a * 6) :
    b * 12 = a * 16 := by
  linarith