import Mathlib

theorem algebra_3588 {a b c d : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = a * x^3 + b * x^2 + c * x + d)
    (h₁ : f (-1) = 4) (h₂ : f 0 = 7) (h₃ : f 1 = 10) (h₄ : f 2 = 25) :
    a + 2 * b + 3 * c + 4 * d = 33 := by
  have eq1 := h₀ (-1)
  rw [eq1] at h₁
  have eq2 := h₀ 0
  rw [eq2] at h₂
  have eq3 := h₀ 1
  rw [eq3] at h₃
  have eq4 := h₀ 2
  rw [eq4] at h₄
  linarith