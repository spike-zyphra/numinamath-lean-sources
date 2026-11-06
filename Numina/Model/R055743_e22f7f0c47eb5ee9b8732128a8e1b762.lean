import Mathlib

theorem algebra_200315 (x1 x2 x3 : ℝ) (hx1 : x1 < 1) (hx2 : x2 < 1) (hx3 : x3 < 1)
    (h : 2*(x1+x2+x3)+4*x1*x2*x3=3*(x1*x2+x1*x3+x2*x3)+1) :
    x1+x2+x3 ≤ 3/4 := by
  have h_pos : (1 - x1) > 0 := by linarith
  have h_pos' : (1 - x2) > 0 := by linarith
  have h_pos'' : (1 - x3) > 0 := by linarith
  
  nlinarith [sq_nonneg (x1 - 1/4), sq_nonneg (x2 - 1/4), sq_nonneg (x3 - 1/4),
          h, mul_pos h_pos h_pos', mul_pos h_pos h_pos'', mul_pos h_pos' h_pos'']