import Mathlib

theorem algebra_3390 {a b : ℝ} (h₀ : a + b = 8) (h₁ : a * b = 6) : a^3 + b^3 = 368 := by
  have h2 : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by
    ring
  rw [h2, h₀, h₁]
  norm_num