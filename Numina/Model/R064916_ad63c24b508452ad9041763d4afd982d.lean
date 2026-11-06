import Mathlib

open Real

theorem algebra_6195 : sqrt (129 - 20 * sqrt 5) = 5 * sqrt 5 - 2 := by 
  have h1 : (5 * sqrt 5 - 2)^2 = 129 - 20 * sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  
  have h2 : 0 ≤ 5 * sqrt 5 - 2 := by
    have h3 : 1 < sqrt 5 := by
      rw [Real.lt_sqrt] <;> norm_num
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]

  rw [← h1]
  rw [Real.sqrt_sq]
  all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]