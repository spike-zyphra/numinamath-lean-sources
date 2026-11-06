import Mathlib

open Filter

theorem inequalities_180447 (x y : Fin 3 → ℝ)
    (h : ∑ i, (x i)^2 ≤ 1) :
    (∑ i, x i * y i - 1)^2 ≥ (∑ i, (x i)^2 - 1) * (∑ i, (y i)^2 - 1) := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, mul_add, add_mul] at h ⊢
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 2 - x 2 * y 0), sq_nonneg (x 1 * y 2 - x 2 * y 1),
    sq_nonneg (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1), sq_nonneg (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1),
    sq_nonneg (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)), sq_nonneg (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)), sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1), sq_nonneg (x 2 - y 2)]