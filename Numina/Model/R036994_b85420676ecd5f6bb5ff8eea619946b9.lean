import Mathlib

open Real

theorem algebra_6880 :
    sqrt (28 - 6 * sqrt 3) = 3 * sqrt 3 - 1 := by
  have h1 : (3 * sqrt 3 - 1) ^ 2 = 28 - 6 * sqrt 3 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : 0 ≤ 3 * sqrt 3 - 1 := by
    have h3 : sqrt 3 ≥ 1 := by 
      have h4 : sqrt 3 ≥ sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
      have h5 : sqrt 1 = 1 := Real.sqrt_one
      nlinarith [Real.sqrt_nonneg 3]
    linarith
  rw [← h1]
  rw [Real.sqrt_sq (by linarith)]