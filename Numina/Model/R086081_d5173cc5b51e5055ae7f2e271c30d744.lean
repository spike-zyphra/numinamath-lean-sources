import Mathlib

theorem algebra_282456 (x y : ℝ) (hx : x ≥ -1) (hy : y ≥ -2)
    (h : x - 3 * √(x + 1) = 3 * √(y + 2) - y) :
    x + y ≤ 9 + 3 * √15 := by
  have h1 : x + y = 3 * (√(x + 1) + √(y + 2)) := by 
    nlinarith [h, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (y + 2), 
      Real.sq_sqrt (show x + 1 ≥ 0 by linarith), Real.sq_sqrt (show y + 2 ≥ 0 by linarith)]
  nlinarith [sq_nonneg (√(x + 1) - √(y + 2)), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (y + 2), 
    Real.sq_sqrt (show x + 1 ≥ 0 by linarith), Real.sq_sqrt (show y + 2 ≥ 0 by linarith), 
    Real.sqrt_nonneg 15, Real.sq_sqrt (show (15 : ℝ) ≥ 0 by norm_num), 
    h, h1, 
    mul_self_nonneg (√(x + 1) - √(y + 2)), 
    mul_self_nonneg (√(x + 1) + √(y + 2) - (3 + Real.sqrt 15))
  ]