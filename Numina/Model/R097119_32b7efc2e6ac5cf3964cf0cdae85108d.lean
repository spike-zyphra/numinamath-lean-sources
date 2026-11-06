import Mathlib

theorem algebra_17061 {a b : ℝ} (h₀ : a + b = 10) (h₁ : a * b = 17) :
    a^3 + b^3 = 490 := by
  have h2 : a^3 + b^3 = (a + b)^3 - 3 * (a * b) * (a + b) := by
    ring
  rw [h2, h₀, h₁]
  norm_num