import Mathlib

theorem inequalities_2099 (a b : ℝ) :
    (48 * a ^ 2 + 108 * b ^ 2 + 27 + 144 * a * b - 108 * b - 72 * a) +
    (36 * b ^ 2 + 12 * b + 1) ≥ 0 := by
  nlinarith [ sq_nonneg (a + 3 / 2 * b - 3 / 4), sq_nonneg (6 * b + 1) ]