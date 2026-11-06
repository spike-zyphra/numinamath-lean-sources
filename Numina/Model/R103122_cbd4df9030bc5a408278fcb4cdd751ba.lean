import Mathlib

theorem algebra_21160 {x y : ℝ} (h₀ : 2 * x - y = 3) (h₁ : x + y = 1) : 8 * x - 7 * y = 13 := by
  have eq1 : 8 * x - 7 * y = 5 * (2 * x - y) - 2 * (x + y) := by
    ring
  rw [eq1]
  rw [h₀, h₁]
  all_goals norm_num