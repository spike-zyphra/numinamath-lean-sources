import Mathlib

theorem algebra_2653 {x y : ℝ} (h : x^2 + y^2 + 5 / 4 = 2 * x + y) :
    x ^ y + y ^ x = 3 / 2 := by
  have h1 : (x - 1)^2 + (y - 1/2)^2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1/2)]
  have h2 : x - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1/2)]
  have h3 : y - 1/2 = 0 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1/2)]
  have hx1 : x = 1 := by
    linarith
  have hy1 : y = 1/2 := by
    linarith
  rw [hx1, hy1]
  norm_num
  all_goals linarith
  all_goals norm_num