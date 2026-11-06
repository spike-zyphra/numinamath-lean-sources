import Mathlib

theorem inequalities_600848 (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 1) :
    2^3 ≤ ∏ i, (1 + a i) / (1 - a i) := by
  simp [Finset.prod_fin_eq_prod_range, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.prod_range_succ] at hsum ⊢
  have h1 : a 0 > 0 := ha 0
  have h2 : a 1 > 0 := ha 1
  have h3 : a 2 > 0 := ha 2
  have h4 : a 0 + a 1 + a 2 = 1 := by
    simpa using hsum

  have h5 : 1 - a 0 > 0 := by
    nlinarith

  have h6 : 1 - a 1 > 0 := by
    nlinarith

  have h7 : 1 - a 2 > 0 := by
    nlinarith
  have h8 : (1 + a 0) * (1 + a 1) * (1 + a 2) / ((1 - a 0) * (1 - a 1) * (1 - a 2)) ≥ (8 : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr 
    nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 1 - a 2),
              mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3, h4]
  norm_num at h8 ⊢

  exact h8