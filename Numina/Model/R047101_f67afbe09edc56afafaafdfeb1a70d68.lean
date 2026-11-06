import Mathlib

open Real

theorem inequalities_309689 {x : Fin 3 → ℝ} (hx : ∀ i, 0 < x i)
    (hxp : ∏ i, x i = 1) :
    ∏ i, (x i + 1) ≥ 8 := by
  have hx1 : 0 < x 0 := hx 0
  have hx2 : 0 < x 1 := hx 1
  have hx3 : 0 < x 2 := hx 2
  have h1 : ∏ i : Fin 3, (x i + 1) = (x 0 + 1) * (x 1 + 1) * (x 2 + 1) := by
    simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
  have h2 : ∏ i : Fin 3, x i = x 0 * x 1 * x 2 := by
    simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
  have h3 : x 0 * x 1 * x 2 = 1 := by
    rw [h2] at hxp
    exact hxp
  have h4 : (x 0 + 1) * (x 1 + 1) * (x 2 + 1) ≥ 8 := by
    have h5 : x 0 * x 1 * x 2 = 1 := h3
    nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 1), sq_nonneg (x 2 - 1),
        sq_nonneg (x 0 * x 1 - 1), sq_nonneg (x 0 * x 2 - 1), sq_nonneg (x 1 * x 2 - 1),
        mul_pos hx1 hx2, mul_pos hx2 hx3, mul_pos hx1 hx3
      ]
  rw [h1]
  linarith [h4]