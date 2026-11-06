import Mathlib

theorem algebra_3968 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 14 = 10 * 60 + 5 * 10) (h2 : b * 14 = 10 * 60 + 3 * 10) :
    b * 14 = 10 * 60 + 1 * 10 + 20 := by
  linarith