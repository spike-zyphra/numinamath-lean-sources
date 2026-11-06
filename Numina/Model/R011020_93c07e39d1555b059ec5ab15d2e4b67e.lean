import Mathlib

open Real

theorem algebra_27 : sqrt ((1 - sqrt 2)^2) + (Real.pi - 3.14)^0 - 3 * sqrt (1 / 2) = -sqrt 2 / 2 := by 
  have h1 : sqrt ((1 - sqrt 2) ^ 2) = sqrt 2 - 1 := by
    have h2 : sqrt ((1 - sqrt 2 : ℝ) ^ 2) = |1 - sqrt 2| := by 
      rw [Real.sqrt_sq_eq_abs]
    have h3 : (1 : ℝ) < sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 1)]
    have h4 : (1 - sqrt 2 : ℝ) < 0 := by
      linarith
    have h5 : sqrt ((1 - sqrt 2) ^ 2) = sqrt 2 - 1 := by 
      rw [h2]
      rw [abs_of_neg h4]
      all_goals 
        ring
    exact h5
  have h2 : (Real.pi - 3.14 : ℝ) ^ 0 = 1 := by 
    simp
  have h3 : sqrt (1 / 2) = Real.sqrt 2 / 2 := by 
    have h4 : sqrt (1 / 2) = sqrt 1 / sqrt 2 := by 
      field_simp [Real.sqrt_div]
    have h5 : sqrt 1 = 1 := by 
      rw [Real.sqrt_one]
    rw [h5] at h4 
    have h6 : sqrt (1 / 2) = Real.sqrt 2 / 2 := by 
      rw [h4]
      have h7 : sqrt 2 > 0 := by 
        positivity
      field_simp [h7]
    linarith
  rw [h1, h2, h3]
  ring_nf