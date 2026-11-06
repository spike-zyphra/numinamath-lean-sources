import Mathlib

theorem algebra_285817 {x y : ℝ} (h₀ : x + y = 12) (h₁ : x * y = 50) :
    x^2 + y^2 = 44 := by
  have h2 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring
  rw [h2, h₀, h₁]
  norm_num