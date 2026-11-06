import Mathlib

theorem algebra_161467 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 5 = b * 5 + 400) (h2 : b * 5 = a * 5 + 40) :
    a * 10 = b * 10 + 180 := by
  linarith