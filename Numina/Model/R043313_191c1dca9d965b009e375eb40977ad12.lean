import Mathlib

theorem inequalities_88728 (x y z : ℝ) : (x ^ 2 + 3) * (y ^ 2 + 3) * (z ^ 2 + 3) ≥
    (x * y * z + x + y + z + 4) ^ 2 := by 
  nlinarith [ sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1),  
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),  
      sq_nonneg (x*y - 1), sq_nonneg (y*z - 1), sq_nonneg (z*x - 1),  
      sq_nonneg (x*y*z - 1) ]