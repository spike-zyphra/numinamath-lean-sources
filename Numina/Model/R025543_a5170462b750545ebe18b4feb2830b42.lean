import Mathlib

theorem inequalities_67656 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 + y ^ 2 + 1 ≤ Real.sqrt ((x ^ 3 + y + 1) * (y ^ 3 + x + 1)) := by 
  have h2 : (x ^ 2 + y ^ 2 + 1 ) ^ 2 ≤ (x ^ 3 + y + 1 ) * (y ^ 3 + x + 1 ) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 3 - y ^ 3), mul_nonneg hx hy, mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), sq_nonneg (x + y - 1), sq_nonneg (x + y), sq_nonneg (x * y - x), sq_nonneg (x * y - y), sq_nonneg (x * (x - y)), sq_nonneg (y * (y - x))]
  
  have h4 : Real.sqrt ((x^3 + y + 1) * (y^3 + x + 1)) ≥ (x ^ 2 + y ^ 2 + 1 ) := by
    have h5 : (x ^ 2 + y ^ 2 + 1 ) ^ 2 ≤ (x ^ 3 + y + 1 ) * (y ^ 3 + x + 1 ) := h2
    have h8 : (Real.sqrt ((x ^ 3 + y + 1 ) * (y ^ 3 + x + 1 )) ) ^ 2 = (x ^ 3 + y + 1 ) * (y ^ 3 + x + 1 ) := by
      rw [Real.sq_sqrt]
      positivity 
    nlinarith [Real.sqrt_nonneg ((x ^ 3 + y + 1 ) * (y ^ 3 + x + 1 )), h5, h8, sq_nonneg (Real.sqrt ((x ^ 3 + y + 1 ) * (y ^ 3 + x + 1 )) - (x ^ 2 + y ^ 2 + 1 ))]
  linarith [h4]