import Mathlib

theorem inequalities_232495 (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i) :
    ∑ i, x i ^ 2 ≥ x 0 * (x 1 + x 2 + x 3 + x 4) := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

  nlinarith [sq_nonneg (x 0 - (x 1 + x 2 + x 3 + x 4) / 2),
      sq_nonneg (x 1 - x 2),
      sq_nonneg (x 1 - x 3),
      sq_nonneg (x 1 - x 4),
      sq_nonneg (x 2 - x 3),
      sq_nonneg (x 2 - x 4),
      sq_nonneg (x 3 - x 4),
      hx 0, hx 1, hx 2, hx 3, hx 4
    ]