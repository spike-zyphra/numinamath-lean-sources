import Mathlib

theorem algebra_10722 {x y : ℝ} (h₀ : (x + y) ^ 2 = 45) (h₁ : x * y = 10) :
    (x - y) ^ 2 = 5 := by 
  have h2 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by 
    ring 
  rw [h2, h₀, h₁]
  all_goals norm_num