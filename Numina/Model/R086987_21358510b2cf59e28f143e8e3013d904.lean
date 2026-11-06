import Mathlib

theorem algebra_221005 (x : ℕ → ℝ)
    (h₁ : ∑ k in Finset.Icc 1 7, k^2 * x k = 1)
    (h₂ : ∑ k in Finset.Icc 1 7, (k + 1)^2 * x k = 12)
    (h₃ : ∑ k in Finset.Icc 1 7, (k + 2)^2 * x k = 123) :
    ∑ k in Finset.Icc 1 7, (k + 3)^2 * x k = 334 := by
  simp [Finset.sum_Icc_succ_top, add_mul, mul_add] at h₁ h₂ h₃ ⊢
  ring_nf at h₁ h₂ h₃ ⊢
  linarith