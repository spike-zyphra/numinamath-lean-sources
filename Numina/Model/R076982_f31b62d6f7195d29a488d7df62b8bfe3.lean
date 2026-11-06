import Mathlib

theorem inequalities_303415 (x : Fin 3 → ℝ) :
    ∑ i, x i ^ 2 ≥ (1 / 3) * (x 0 + x 1 + x 2) ^ 2 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2),
    sq_nonneg (x 0 + x 1 + x 2), sq_nonneg (x 0 - (x 1 + x 2) / 2), sq_nonneg (x 1 - (x 0 + x 2) / 2), sq_nonneg (x 2 - (x 0 + x 1) / 2)
  ]