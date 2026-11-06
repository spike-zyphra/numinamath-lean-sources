import Mathlib

theorem inequalities_602935 (x y : ℝ) : 3 * (x + y + 1) ^ 2 + 1 ≥ 3 * x * y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 1), sq_nonneg (x + y - (-4 / 3)), sq_nonneg (x - y), sq_nonneg (3 * (x + y) + 4), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x + y + 1 - (x * y)), mul_self_nonneg (x - y), mul_self_nonneg (x + y - 2)]