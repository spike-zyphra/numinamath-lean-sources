import Mathlib

theorem inequalities_170635 (a b c : ℝ) (h : (a + b + c) * c ≤ 0) :
    b^2 ≥ 4 * a * c := by
  nlinarith [sq_nonneg (b + 2 * c), sq_nonneg (c + a), sq_nonneg (b - 2 * c), sq_nonneg (c + (a)), sq_nonneg (b + 2 * a), sq_nonneg ((a + b + c) + c), sq_nonneg ((a + b) - 2 * c), sq_nonneg ((2 * c + a + b)), sq_nonneg ((b + a) - 2 * c)]