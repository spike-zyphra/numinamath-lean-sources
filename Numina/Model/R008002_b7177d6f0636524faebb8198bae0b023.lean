import Mathlib

theorem algebra_15589 {x y : ℝ} (h₀ : x + 2 * y = 4) (h₁ : x * y = -8) :
    x ^ 2 + 4 * y ^ 2 = 48 := by
  have h2 : x ^ 2 + 4 * y ^ 2 = (x + 2 * y) ^ 2 - 4 * (x * y) := by
    ring
  rw [h2, h₀, h₁]
  norm_num