import Mathlib

theorem number_theory_258777 : (729 : ℝ) ^ ((1 : ℝ) / 3) < (121 : ℝ) ^ ((1 : ℝ) / 2) ∧
    (121 : ℝ) ^ ((1 : ℝ) / 2) < (38416 : ℝ) ^ ((1 : ℝ) / 4) := by

  have h1 : (729 : ℝ) ^ ((1 : ℝ) / 3) = 9 := by
    have h2 : (729 : ℝ) ^ ((1 : ℝ) / 3) = (9 : ℝ) := by
      rw [show (729 : ℝ) = 9 ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith

  have h3 : (121 : ℝ) ^ ((1 : ℝ) / 2) = 11 := by
    have h4 : (121 : ℝ) ^ ((1 : ℝ) / 2) = (11 : ℝ) := by
      rw [show (121 : ℝ) = 11 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith

  have h5 : (38416 : ℝ) ^ ((1 : ℝ) / 4) = 14 := by
    have h6 : (38416 : ℝ) ^ ((1 : ℝ) / 4) = (14 : ℝ) := by
      rw [show (38416 : ℝ) = 14 ^ (4 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith

  constructor
  · -- Show that (729 : ℝ) ^ ((1 : ℝ) / 3) < (121 : ℝ) ^ ((1 : ℝ) / 2)
    rw [h1, h3]
    all_goals norm_num

  · -- Show that (121 : ℝ) ^ ((1 : ℝ) / 2) < (38416 : ℝ) ^ ((1 : ℝ) / 4)
    rw [h3, h5]
    all_goals norm_num