import Mathlib

theorem algebra_19779 : (8 : ℝ) ^ ((1 : ℝ) / 8) < Real.sqrt 2 ∧ (8 : ℝ) ^ ((1 : ℝ) / 8) < 4 ^ ((1 : ℝ) / 4) := by
  have h1 : (8 : ℝ) ^ ((1 : ℝ) / 8) < Real.sqrt 2 := by
    have h2 : (8 : ℝ) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ (3 / 8 : ℝ) := by
      have h3 : (8 : ℝ) ^ ((1 : ℝ) / 8) = ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 8) := by norm_num
      rw [h3]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h4 : Real.sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
      have h5 : Real.sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h5]
    rw [h2, h4]
    have h5 : (2 : ℝ) ^ (3 / 8 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals norm_num
    linarith
  have h2 : (8 : ℝ) ^ ((1 : ℝ) / 8) < 4 ^ ((1 : ℝ) / 4) := by
    have h3 : (8 : ℝ) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ (3 / 8 : ℝ) := by
      have h4 : (8 : ℝ) ^ ((1 : ℝ) / 8) = ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 8) := by norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
      have h5 : (4 : ℝ) ^ ((1 : ℝ) / 4) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) := by norm_num
      rw [h5]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h3, h4]
    have h5 : (2 : ℝ) ^ (3 / 8 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals norm_num
    linarith
  constructor
  · exact h1
  · exact h2