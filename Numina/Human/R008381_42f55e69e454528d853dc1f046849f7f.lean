import Mathlib

theorem algebra_91553 {x y z : ℝ} (h1 : x + y = 2) (h2 : x * y = z ^ 2 + 1) :
    x ^ 2 + y ^ 2 + z ^ 2 = 2 := by 
  have h3 : (x + y) ^ 2 = 4 := by 
    rw [h1]
    norm_num
  have h4 : x ^ 2 + y ^ 2 = 2 - 2 * z ^ 2 := by 
    linarith [sq_nonneg (x - y), sq_nonneg (z)]
  linarith [sq_nonneg (x - y), sq_nonneg (z)]