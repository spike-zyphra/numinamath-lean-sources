import Mathlib

theorem algebra_300996 {a b : ℝ} (h₁ : (a + b)^2 = 8) (h₂ : (a - b)^2 = 12) :
    a^2 + b^2 = 10 := by
  have eq1 : (a + b) ^ 2 = a^2 + 2 * a * b + b^2 := by
    ring
  have eq2 : (a - b) ^ 2 = a^2 - 2 * a * b + b^2 := by
    ring
  rw [eq1] at h₁
  rw [eq2] at h₂
  linarith