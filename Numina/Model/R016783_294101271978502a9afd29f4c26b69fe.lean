import Mathlib


theorem inequalities_308723 (x y z : ℝ) (h : (2*x^2+8*x+11)*(y^2-10*y+29)*(3*z^2-18*z+32)≤60) :
    x+y-z=0 := by
  have h1 : 2 * x ^ 2 + 8 * x + 11 ≥ 3 := by
    nlinarith [sq_nonneg (x + 2)]
  have h2 : y ^ 2 - 10 * y + 29 ≥ 4 := by
    nlinarith [sq_nonneg (y - 5)]
  have h3 : 3 * z ^ 2 - 18 * z + 32 ≥ 5 := by
    nlinarith [sq_nonneg (z - 3)]
  have h4 : (2 * x ^ 2 + 8 * x + 11) = 3 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (2 * x ^ 2 + 8 * x + 11 - 3) by nlinarith) (show (0 : ℝ) ≤ (y ^ 2 - 10 * y + 29 - 4) by nlinarith), 
    mul_nonneg (show (0 : ℝ) ≤ (y ^ 2 - 10 * y + 29 - 4) by nlinarith) (show (0 : ℝ) ≤ (3 * z ^ 2 - 18 * z + 32 - 5) by nlinarith), 
    mul_nonneg (show (0 : ℝ) ≤ (2 * x ^ 2 + 8 * x + 11 - 3) by nlinarith) (show (0 : ℝ) ≤ (3 * z ^ 2 - 18 * z + 32 - 5) by nlinarith)]
  have h5 : (3 * z ^ 2 - 18 * z + 32) = 5 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (2 * x ^ 2 + 8 * x + 11 - 3) by nlinarith) (show (0 : ℝ) ≤ (y ^ 2 - 10 * y + 29 - 4) by nlinarith), 
    mul_nonneg (show (0 : ℝ) ≤ (y ^ 2 - 10 * y + 29 - 4) by nlinarith) (show (0 : ℝ) ≤ (3 * z ^ 2 - 18 * z + 32 - 5) by nlinarith), 
    mul_nonneg (show (0 : ℝ) ≤ (2 * x ^ 2 + 8 * x + 11 - 3) by nlinarith) (show (0 : ℝ) ≤ (3 * z ^ 2 - 18 * z + 32 - 5) by nlinarith)]
  have h6 : z = 3 := by
    nlinarith [sq_nonneg (z - 3)]
  have h7 : (y ^ 2 - 10 * y + 29) = 4 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (2 * x ^ 2 + 8 * x + 11 - 3) by nlinarith) (show (0 : ℝ) ≤ (y ^ 2 - 10 * y + 29 - 4) by nlinarith), 
    mul_nonneg (show (0 : ℝ) ≤ (y ^ 2 - 10 * y + 29 - 4) by nlinarith) (show (0 : ℝ) ≤ (3 * z ^ 2 - 18 * z + 32 - 5) by nlinarith), 
    mul_nonneg (show (0 : ℝ) ≤ (2 * x ^ 2 + 8 * x + 11 - 3) by nlinarith) (show (0 : ℝ) ≤ (3 * z ^ 2 - 18 * z + 32 - 5) by nlinarith)]
  have h8 : y = 5 := by
    nlinarith [sq_nonneg (y - 5)]
  have h10 : x = -2 := by
    nlinarith [sq_nonneg (x + 2)]
  linarith [h10, h8, h6]