import Mathlib

theorem inequalities_212246 (x : Fin 3 → ℝ)
    (h₀ : ∀ i, 0 ≤ x i)
    (h₁ : ∑ i, x i ≤ 1 / 2) :
    ∏ i, (1 - x i) ≥ 1 / 2 := by 
  simp [Finset.prod_fin_eq_prod_range, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.prod_range_succ] at h₁ ⊢
  have hx0 : 0 ≤ x 0 := h₀ 0
  have hx1 : 0 ≤ x 1 := h₀ 1
  have hx2 : 0 ≤ x 2 := h₀ 2
  have h2 : x 0 + x 1 + x 2 ≤ 1 / 2 := by 
    linarith
  nlinarith [sq_nonneg (x 0 - 1 / 2), sq_nonneg (x 1 - 1 / 2), sq_nonneg (x 2 - 1 / 2), sq_nonneg (x 0 + x 1 + x 2 - 1 / 2), mul_nonneg hx0 hx1, mul_nonneg hx0 hx2, mul_nonneg hx1 hx2]