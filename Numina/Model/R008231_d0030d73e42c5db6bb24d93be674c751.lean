import Mathlib

theorem algebra_19278 {x y : ℝ} (h₀ : (2 * x + 3 * y) ^ 2 = 4) (h₁ : x * y = -5) :
    4 * x ^ 2 + 9 * y ^ 2 = 64 := by 
  have h2 : 4 * x ^ 2 + 9 * y ^ 2 = (2 * x + 3 * y) ^ 2 - 12 * (x * y) := by 
    ring
  rw [h2, h₀, h₁]
  norm_num