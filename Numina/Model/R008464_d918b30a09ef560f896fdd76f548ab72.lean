import Mathlib

theorem algebra_14923 {x y : ℝ} (h₀ : x + y = 9) (h₁ : x * y = 10) :
    x ^ 3 + y ^ 3 = 459 := by
  have h2 : x^3 + y^3 = (x + y)^3 - 3 * (x * y) * (x + y) := by
    ring
  rw [h2, h₀, h₁]
  norm_num