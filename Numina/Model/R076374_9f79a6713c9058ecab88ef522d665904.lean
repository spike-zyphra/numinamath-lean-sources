import Mathlib

theorem algebra_278079 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * (1 / 2) = b * (1 / 3)) (h2 : a * (2 / 3) = b * (1 / 2)) :
    a * 2 = b * 3 := by
  nlinarith