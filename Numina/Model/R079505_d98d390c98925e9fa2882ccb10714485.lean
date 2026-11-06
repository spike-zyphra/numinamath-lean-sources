import Mathlib

theorem algebra_277577 (a b c d : ℝ) (f : ℝ → ℝ)
    (h₀ : f 1 = 0) (h₁ : f 2 = 0) (h₂ : f 3 = 0)
    (h₃ : ∀ x, f x = x^4 + a * x^3 + b * x^2 + c * x + d) :
    f 0 + f 4 = 24 := by
  norm_num [h₃] at h₀ h₁ h₂ ⊢
  linarith