import Mathlib

theorem algebra_13808 {a b : ℝ} (h₀ : a + b = 7) (h₁ : a ^ 3 + b ^ 3 = 91) : a * b = 12 := by
  have h2 : a ^ 3 + b ^ 3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by
    ring
  rw [h₀] at h2
  rw [h₁] at h2
  nlinarith