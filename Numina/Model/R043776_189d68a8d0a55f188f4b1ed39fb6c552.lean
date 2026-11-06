import Mathlib

open Real

theorem algebra_268730 :
    (√(2 + √3) * √(2 + √(2 + √3)) * √(2 + √(2 + √(2 + √3))) *
     √(2 - √(2 + √(2 + √3)))) = 1 := by
  have h1 : √(2 + √3) * √(2 + √(2 + √3)) * √(2 + √(2 + √(2 + √3))) *
  √(2 - √(2 + √(2 + √3))) =
  √((2 + √3) * (2 + √(2 + √3)) * (2 + √(2 + √(2 + √3))) * (2 - √(2 + √(2 + √3)))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [h1] at *
  have h2 : ((2 + √3) * (2 + √(2 + √3)) * (2 + √(2 + √(2 + √3))) * (2 - √(2 + √(2 + √3)))) = 1 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (2 + √3), Real.sqrt_nonneg (2 + √(2 + √3)), Real.sqrt_nonneg (2 + √(2 + √(2 + √3))), Real.sqrt_nonneg (2 - √(2 + √(2 + √3))), sq_nonneg (√3 - 1), sq_nonneg (√(2 + √3) - 1), sq_nonneg (√(2 + √(2 + √3)) - 1), sq_nonneg (√(2 + √3) ^ 2 - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + √3 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + √(2 + √3) : ℝ) by positivity), Real.sqrt_nonneg (2 + √(2 + √3)), Real.sqrt_nonneg (2 + √3), Real.sqrt_nonneg (2 + √(2 + √(2 + √3))), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + √(2 + √3) : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + √3 : ℝ) by positivity), sq_nonneg (√3 ^ 2 - 3), sq_nonneg ((√(2 + √3)) ^ 2 - (2 + √3)), sq_nonneg ((√(2 + √(2 + √3))) ^ 2 - (2 + √(2 + √3))), sq_nonneg ((√(2 - √(2 + √(2 + √3)))) ^ 2 - (2 - √(2 + √(2 + √3)))), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (2 + √3)), mul_nonneg (Real.sqrt_nonneg (2 + √3)) (Real.sqrt_nonneg (2 + √(2 + √3))), mul_nonneg (Real.sqrt_nonneg (2 + √(2 + √3))) (Real.sqrt_nonneg (2 - √(2 + √(2 + √3))))]
  rw [h2]
  all_goals norm_num