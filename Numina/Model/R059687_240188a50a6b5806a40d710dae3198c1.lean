import Mathlib

theorem algebra_297707 : (4 * X ^ 4 - 4 * X ^ 3 - 14 * X ^ 2 + 12 * X + 6) =
    (X + Real.sqrt 3) * (X - Real.sqrt 3) * (2 * X - 1 + Real.sqrt 3) * (2 * X - 1 - Real.sqrt 3) := by
  ring_nf
  <;> norm_num [Real.sqrt_mul_self, Real.sqrt_nonneg]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  all_goals
    ring_nf
    <;> norm_num [Real.sqrt_mul_self, Real.sqrt_nonneg, Real.sq_sqrt]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]