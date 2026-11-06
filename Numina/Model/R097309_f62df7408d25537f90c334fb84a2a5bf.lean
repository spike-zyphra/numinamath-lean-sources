import Mathlib

theorem inequalities_276924 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a ≥ b) :
    (a ^ 4 + b ^ 4) / 2 ≥ ((a + b) / 2) ^ 4 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - a*b), sq_nonneg (b^2 - a*b), mul_pos ha hb, sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]