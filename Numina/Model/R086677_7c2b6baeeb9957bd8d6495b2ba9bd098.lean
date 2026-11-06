import Mathlib

theorem algebra_182335 (a b c d : ℝ) (p : ℝ → ℝ)
    (h₀ : ∀ x, p x = x^4 + a * x^3 + b * x^2 + c * x + d)
    (h₁ : p 1 = 1993) (h₂ : p 2 = 3986) (h₃ : p 3 = 5979) :
    (p 11 + p (-7)) / 4 = 5233 := by 
  have eq1 := h₀ 1
  rw [eq1] at h₁
  have eq2 := h₀ 2
  rw [eq2] at h₂
  have eq3 := h₀ 3
  rw [eq3] at h₃
  have eq11 := h₀ 11
  have eq7 := h₀ (-7)
  rw [eq11, eq7]
  linarith