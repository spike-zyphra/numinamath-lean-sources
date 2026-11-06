import Mathlib

theorem algebra_187041 (a d : ℝ) (h₀ : a + 2 * d = -5) (h₁ : a + 4 * d = 2.4) :
    15 * a + 105 * d = 202.5 := by 
  ring_nf at h₀ h₁ ⊢
  linarith