import Mathlib

theorem algebra_17050 {x y : ℝ} (h₀ : x * y = 6) (h₁ : x ^ 2 * y + x * y ^ 2 + x + y = 63) :
    x ^ 2 + y ^ 2 = 69 := by
  have h3 : x + y = 9 := by
    have eq1 : x^2 * y + x * y^2 = x * y * (x + y) := by
      ring
    rw [eq1] at h₁
    rw [h₀] at h₁
    linarith
  have h4 : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by
    ring
  rw [h4, h3, h₀]
  norm_num