import Mathlib

theorem algebra_76 (total_milk : ℝ) (h : total_milk = 8) (recipe_milk : ℝ) (h2 : recipe_milk = 1 + 2 / 5)
    (num_children : ℕ) (h3 : num_children = 3) :
    (total_milk - recipe_milk) / num_children = 2 + 1 / 5 := by
  rw [h, h2, h3]
  norm_num