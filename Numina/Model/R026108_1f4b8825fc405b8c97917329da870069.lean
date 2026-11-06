import Mathlib

theorem inequalities_597807 (x y : Fin 3 → ℝ) (h : ∑ i, x i ^ 2 ≤ 1) :
    (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - 1) ^ 2 ≥
    (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1) * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - 1) := by

  have h1 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ 1 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
    linarith
  nlinarith [sq_nonneg (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)), 
            sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1), sq_nonneg (x 2 - y 2),
            sq_nonneg (x 0 + y 0), sq_nonneg (x 1 + y 1), sq_nonneg (x 2 + y 2),
            sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 2 - x 2 * y 0), sq_nonneg (x 1 * y 2 - x 2 * y 1)
            ]