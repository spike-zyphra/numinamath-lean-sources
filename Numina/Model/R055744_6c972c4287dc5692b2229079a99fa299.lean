import Mathlib

theorem algebra_198798 (a : Fin 6 → ℝ) (h₀ : ∑ i, a i = 162)
    (h₁ : ∑ i in Finset.range 4, a i = 92) (h₂ : ∑ i in Finset.range 3, a (5 - i) = 102) :
    a 3 = 32 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h₀ h₁ h₂
  linarith