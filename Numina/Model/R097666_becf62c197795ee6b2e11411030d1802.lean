import Mathlib

theorem algebra_11834 (a b c d : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (h₁ : f 1 = 2) (h₂ : f 2 = 4) (h₃ : f 3 = 6) :
    f 0 + f 4 = 32 := by
  have eq1 := h₀ 1
  rw [eq1] at h₁
  have eq2 := h₀ 2
  rw [eq2] at h₂
  have eq3 := h₀ 3
  rw [eq3] at h₃
  have eq0 := h₀ 0
  have eq4 := h₀ 4
  simp at eq0 eq4
  simp [eq0, eq4]
  linarith