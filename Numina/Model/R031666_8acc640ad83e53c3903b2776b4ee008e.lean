import Mathlib

theorem algebra_288737 : ⌊(2010^3 + 3 * 2010^2 + 4 * 2010 + 1 : ℝ) ^ ((1 : ℝ) / 3)⌋ = 2011 := by
  have h1 : (2010^3 + 3 * 2010^2 + 4 * 2010 + 1 : ℝ) = (2011 ^ 3 + (2010 : ℝ)) := by
    norm_num
  rw [h1]
  have h2 : (2011: ℝ) < ((2011 ^ 3 + (2010: ℝ)) ^ ((1: ℝ) / 3)) := by
    have h3 : (2011 : ℝ) ^ (3: ℝ) < (2011 ^ 3 + (2010: ℝ)) := by
      norm_num
    have h5 : ((2011: ℝ) ^ (3: ℝ)) ^ ((1: ℝ) / 3) = (2011: ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h6 : ((2011 ^ 3 + (2010: ℝ)) ^ ((1: ℝ) / 3)) > ((2011: ℝ) ^ (3: ℝ) ) ^ ((1: ℝ) / 3) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith
    nlinarith [h5, h6]
  have h3 : ((2011 ^ 3 + (2010: ℝ)) ^ ((1: ℝ) / 3)) < (2012: ℝ) := by
    have h7 : (2011 ^ 3 + (2010: ℝ)) < (2012: ℝ) ^ (3: ℝ) := by
      norm_num
    have h8 : ((2012: ℝ) ^ (3: ℝ)) ^ ((1: ℝ) / 3) = (2012: ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h9 : ((2011 ^ 3 + (2010: ℝ)) ^ ((1: ℝ) / 3)) < (( (2012: ℝ) ^ (3: ℝ)) ^ ((1: ℝ) / 3)) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith
    nlinarith [h9, h8]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try linarith)