import Mathlib

theorem algebra_315987 {a b c d : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x^4 + a * x^3 + b * x^2 + c * x + d)
    (h₁ : f 1 = 10) (h₂ : f 2 = 20) (h₃ : f 3 = 30) :
    f 10 + f (-6) = 8104 := by
  have h_eq1 := h₀ 1
  rw [h_eq1] at h₁
  have h_eq2 := h₀ 2
  rw [h_eq2] at h₂
  have h_eq3 := h₀ 3
  rw [h_eq3] at h₃
  have h_eq10 := h₀ 10
  have h_eq_neg6 := h₀ (-6)
  rw [h_eq10, h_eq_neg6]
  linarith