import Mathlib

theorem inequalities_276885 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 4 + b ^ 4 ≥ a ^ 3 * b + a * b ^ 3 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a ^ 2 + b ^ 2 - a * b), mul_pos ha hb]