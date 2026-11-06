import Mathlib

theorem inequalities_61956 (x : Fin 3 → ℝ) (h : ∀ i, 0 ≤ x i)
    (h' : ∑ i, x i ≤ 1 / 2) :
    ∏ i, (1 - x i) ≥ 1 / 2 := by
  simp [Finset.prod_fin_eq_prod_range, Finset.sum_fin_eq_sum_range, Finset.prod_range_succ, Finset.sum_range_succ] at *
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2),
    h 0, h 1, h 2,
    mul_nonneg (h 0) (h 1), mul_nonneg (h 0) (h 2), mul_nonneg (h 1) (h 2)]