import Mathlib

theorem algebra_95745 {x b : ℝ} (h₁ : 2 * x + 7 = 3) (h₂ : b * x - 10 = - 2) :
b = -4 := by
  have hx : x = -2 := by
    linarith
  rw [hx] at h₂
  linarith