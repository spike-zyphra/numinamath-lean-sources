import Mathlib

open Real

theorem algebra_172414 {A B : ℝ}
    (hA : A = (1 + 2 * sqrt 2 + 3 * sqrt 3 + 6 * sqrt 6) * (2 + 6 * sqrt 2 + sqrt 3 + 3 * sqrt 6) * (3 + sqrt 2 + 6 * sqrt 3 + 2 * sqrt 6) * (6 + 3 * sqrt 2 + 2 * sqrt 3 + sqrt 6))
    (hB : B = (1 + 3 * sqrt 2 + 2 * sqrt 3 + 6 * sqrt 6) * (2 + sqrt 2 + 6 * sqrt 3 + 3 * sqrt 6) * (3 + 6 * sqrt 2 + sqrt 3 + 2 * sqrt 6) * (6 + 2 * sqrt 2 + 3 * sqrt 3 + sqrt 6)) :
    A / B = 1 := by
  have h1 : sqrt 6 = sqrt 2 * sqrt 3 := by
    calc
      sqrt 6 = sqrt (2 * 3) := by norm_num
      _ = sqrt 2 * sqrt 3 := by rw [Real.sqrt_mul]; linarith
  rw [h1] at hA hB
  rw [hA, hB]
  field_simp [
    show sqrt 2 ≠ 0 from by positivity, 
    show sqrt 3 ≠ 0 from by positivity, 
    sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
    sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
    mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 3 by norm_num)
  ]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 + sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (sqrt 2 ^ 2 - sqrt 3 ^ 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 3 by norm_num), sq_nonneg (sqrt 2 * sqrt 3)]