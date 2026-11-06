import Mathlib

open Real

theorem inequalities_33316 (a : ℝ) (ha : a = 2 * sqrt 2) (x y z : ℝ) :
    abs (x - y) + abs (y - z) + abs (z - x) ≤ a * sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by 
  rw [ha]
  have h1 : (abs (x - y) + abs (y - z) + abs (z - x)) ^ 2 ≤ 8 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    cases' abs_cases (x - y) with hxy hxy <;> 
    cases' abs_cases (y - z) with hyz hyz <;> 
    cases' abs_cases (z - x) with hzx hzx <;> 
      nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y - z), sq_nonneg (y - x - z), sq_nonneg (z - x - y), Real.sqrt_nonneg (2), Real.sqrt_nonneg (x ^ 2 + y ^ 2 + z ^ 2),
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + y ^ 2 + z ^ 2 : ℝ) by positivity), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h2 : abs (x - y) + abs (y - z) + abs (z - x) ≤ 2 * Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by 
    have h3 : (abs (x - y) + abs (y - z) + abs (z - x)) ^ 2 ≤ 8 * (x ^ 2 + y ^ 2 + z ^ 2) := h1
    have h4 : (2 * Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 = 8 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      calc
        (2 * Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2
          = 4 * (Real.sqrt 2) ^ 2 * (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 := by ring
        _ = 4 * 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by 
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + y ^ 2 + z ^ 2 by positivity)]
          all_goals linarith
        _ = 8 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring
    have h5 : abs (x - y) + abs (y - z) + abs (z - x) ≥ 0 := by 
      cases' abs_cases (x - y) with hxy hxy <;> 
      cases' abs_cases (y - z) with hyz hyz <;> 
      cases' abs_cases (z - x) with hzx hzx <;> 
        nlinarith
    have h6 : (2 * Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ≥ 0 := by 
      positivity
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (x ^ 2 + y ^ 2 + z ^ 2), 
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (x ^ 2 + y ^ 2 + z ^ 2)), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  linarith [h2]