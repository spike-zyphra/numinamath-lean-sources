import Mathlib

theorem algebra_13651 : round ((100 : ℝ) ^ ((1 : ℝ) / 3)) = 5 := by
  have h2 : (100 : ℝ) ^ ((1 : ℝ) / 3) > (4.5 : ℝ) := by
    have h3 : (100 : ℝ) ^ ((1 : ℝ) / 3) > (91.125 : ℝ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_lt_rpow
      all_goals norm_num
    have h4 : (91.125 : ℝ) ^ ((1 : ℝ) / 3) = (4.5 : ℝ) := by
      have h5 : (91.125 : ℝ) = (4.5 : ℝ) ^ 3 := by norm_num
      rw [h5]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith

  have h3 : (100 : ℝ) ^ ((1 : ℝ) / 3) < (5.5 : ℝ) := by
    have h4 : (100 : ℝ) ^ ((1 : ℝ) / 3) < (166.375 : ℝ) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_lt_rpow
      all_goals norm_num
    have h5 : (166.375 : ℝ) ^ ((1 : ℝ) / 3) = (5.5 : ℝ) := by
      have h6 : (166.375 : ℝ) = (5.5 : ℝ) ^ 3 := by norm_num
      rw [h6]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    linarith
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith