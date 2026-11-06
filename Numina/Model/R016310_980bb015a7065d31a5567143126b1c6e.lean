import Mathlib

theorem inequalities_300559 (x y : ℝ) (hx : abs x < 1) (hy : abs y < 1) :
    2 / (1 - x * y) ≤ 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) := by

  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : -1 < y := by linarith [abs_lt.mp hy]
  have h4 : y < 1 := by linarith [abs_lt.mp hy]

  have h5 : 0 < 1 - x ^ 2 := by
    nlinarith
  have h6 : 0 < 1 - y ^ 2 := by
    nlinarith
  have h7 : 0 < 1 - x * y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  
  have h8 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) ≥ 0 := by 
    have h' : 0 < (1 - x^2) * (1 - y^2) * (1 - x * y) := by
      positivity
  
    have h9 : (1 - y^2) * (1 - x * y) + (1 - x^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2) ≥ 0 := by 
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - x), sq_nonneg (x * y - y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x * y - x * y), mul_pos (show (0 : ℝ) < 1 - x by linarith) (show (0 : ℝ) < 1 - x by linarith), mul_pos (show (0 : ℝ) < 1 - y by linarith) (show (0 : ℝ) < 1 - y by linarith), mul_pos h5 h6, mul_pos h5 h7, mul_pos h6 h7]

    have h10 : (1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y)) = ( (1 - y^2) * (1 - x * y) + (1 - x^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2) ) / ( (1 - x^2) * (1 - y^2) * (1 - x * y) ) := by 
      field_simp [(show 1 - x ^ 2 ≠ 0 by nlinarith), (show 1 - y ^ 2 ≠ 0 by nlinarith), (show 1 - x * y ≠ 0 by nlinarith)]
      ring
  
    rw [h10]
    apply div_nonneg
    linarith
    all_goals positivity
  
  linarith