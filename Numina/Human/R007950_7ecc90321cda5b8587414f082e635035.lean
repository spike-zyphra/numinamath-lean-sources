import Mathlib

theorem algebra_101550 (a : ℝ) (ha : 0 < a)
    (h1 : 6 * 35 * a = 1/3) :
    35 + (1 - 1/3) / (12 * a) = 70 := by
  field_simp at *
  linarith
