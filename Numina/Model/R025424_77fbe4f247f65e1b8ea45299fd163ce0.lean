import Mathlib

theorem inequalities_90147 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 3) :
    y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 < 3 + y * z + z * x + x * y := by
  have h1 : z = 3 - x - y := by
    linarith
  rw [h1]
  nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos (show (3 - x - y : ℝ) > 0 by 
    nlinarith
  ), mul_pos hx hy, 
            mul_pos hx (show (3 - x - y : ℝ) > 0 by 
              nlinarith
            ), 
            mul_pos hy (show (3 - x - y : ℝ) > 0 by 
              nlinarith
            ), sq_nonneg (x - y), sq_nonneg (x - (3 - x - y)), sq_nonneg (y - (3 - x - y)), sq_nonneg (x + y - (3 - x - y)), mul_pos (show 0 < x * y by nlinarith) (show 0 < (3 - x - y : ℝ) by nlinarith)
           , sq_nonneg (x * y - y * (3 - x - y)), sq_nonneg (x * (3 - x - y) - y * (3 - x - y))
          ]