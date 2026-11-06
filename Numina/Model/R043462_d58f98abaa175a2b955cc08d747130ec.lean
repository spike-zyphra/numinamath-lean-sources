import Mathlib

theorem algebra_182339 {x y : ℝ} (h1 : x^2 + y^2 + x * y = 28) (h2 : 8 * x - 12 * y + x * y = 80) :
    3 * x + 2 * y = 0 := by
  have h3 : (x - 4)^2 + (y + 6)^2 = 0 := by
    nlinarith
  have h4 : x - 4 = 0 := by 
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y + 6)]
  have hx : x = 4 := by 
    linarith 
  have h5 : y + 6 = 0 := by 
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y + 6), hx] 
  have hy : y = -6 := by 
    linarith 
  rw [hx, hy]
  norm_num