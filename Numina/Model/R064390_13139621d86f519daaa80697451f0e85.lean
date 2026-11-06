import Mathlib

theorem algebra_20674 {x y : ℤ} (h₀ : x + y = 25) (h₁ : x - y = 9) :
    x * y = 136 := by 
  have h2 : x = 17 := by
    linarith
  have h3 : y = 8 := by
    linarith
  rw [h2, h3]
  all_goals norm_num