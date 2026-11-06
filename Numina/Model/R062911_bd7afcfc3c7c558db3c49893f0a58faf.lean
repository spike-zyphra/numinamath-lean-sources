import Mathlib

theorem algebra_129772 (x y : ℝ) (h₀ : 3 * x + 2 * y = 15.5) (h₁ : 2 * x + 3 * y = 17) :
    4 * x + 4 * y = 26 := by
  ring_nf at h₀ h₁ ⊢
  linarith