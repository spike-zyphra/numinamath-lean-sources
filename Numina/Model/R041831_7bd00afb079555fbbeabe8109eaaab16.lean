import Mathlib

theorem algebra_201814 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 12 * a = 12 * b + 45) (h2 : 13 * a = 13 * b + 45) :
    14 * a = 14 * b + 45 := by
  nlinarith