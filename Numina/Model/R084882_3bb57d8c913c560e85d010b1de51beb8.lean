import Mathlib

theorem algebra_278 {x y z : ℝ} (h₀ : x + 2*y + 3*z = 1.50) (h₁ : 2*x + 3*y + z = 1.00)
    (h₂ : 3*x + y + 2*z = 1.40) :
    x + y + z = 65 / 100 := by
  ring_nf at h₀ h₁ h₂ ⊢
  linarith