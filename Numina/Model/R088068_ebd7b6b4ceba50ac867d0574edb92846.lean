import Mathlib

open Real

theorem algebra_133196 : sqrt (4 + 2 * sqrt 3) + sqrt (4 - 2 * sqrt 3) = 2 * sqrt 3 := by

  have h1 : sqrt (4 + 2 * sqrt 3) = sqrt 3 + 1 := by
    have h2 : 0 ≤ sqrt 3 + 1 := by 
      have h3 : sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
      linarith
    have h4 : (sqrt 3 + 1) ^ 2 = 4 + 2 * sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [← h4]
    field_simp [Real.sqrt_sq, h2]

  have h2 : sqrt (4 - 2 * sqrt 3) = sqrt 3 - 1 := by
    have h3 : 0 ≤ sqrt 3 - 1 := by
      have h4 : 1 < sqrt 3 := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith
    have h5 : (sqrt 3 - 1) ^ 2 = 4 - 2 * sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [← h5]
    field_simp [Real.sqrt_sq, h3]

  rw [h1, h2]
  ring