import Mathlib

theorem algebra_21858 {a b c d : ℝ} (h₀ : a - b = 2 * (c + d)) (h₁ : b = a - 2) (h₂ : d = c + 5) :
    c = -2 := by

  have eq1 : c + d = 1 := by
    rw [h₁] at h₀
    linarith

  rw [h₂] at eq1
  linarith