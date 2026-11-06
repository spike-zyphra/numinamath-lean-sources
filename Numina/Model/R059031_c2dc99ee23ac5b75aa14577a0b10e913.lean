import Mathlib

theorem algebra_105888 (a b c : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = a * x ^ 7 + b * x ^ 3 + c * x - 5)
    (h₁ : f (-7) = 7) :
    f 7 = -17 := by
  have eq1 : f (-7) = a * (-7) ^ 7 + b * (-7) ^ 3 + c * (-7) - 5 := h₀ (-7)
  have eq2 : f 7 = a * 7 ^ 7 + b * 7 ^ 3 + c * 7 - 5 := h₀ 7
  rw [eq1] at h₁
  rw [eq2] at *
  norm_num at h₁ ⊢
  linarith