import Mathlib

theorem algebra_143786 : 9 ^ ((3 : ℝ) / 2) * 8 ^ ((-1 : ℝ) / 3) - Real.sqrt (16 ^ ((5 : ℝ) / 4) - 7) = 17 / 2 := by

  have h1 : (9 : ℝ) ^ ((3 : ℝ) / 2) = 27 := by
    have h11 : (9 : ℝ) = 3 ^ (2 : ℝ) := by norm_num
    rw [h11]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  
  have h2 : (8 : ℝ) ^ ((-1 : ℝ) / 3) = 1 / 2 := by
    have h21 : (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
    rw [h21]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  
  have h3 : (9 : ℝ) ^ ((3 : ℝ) / 2) * (8 : ℝ) ^ ((-1 : ℝ) / 3) = 27 / 2 := by
    rw [h1, h2]
    all_goals norm_num
  
  have h4 : (16 : ℝ) ^ ((5 : ℝ) / 4) = 32 := by
    have h41 : (16 : ℝ) = 2 ^ (4 : ℝ) := by norm_num
    rw [h41]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  
  have h5 : (16 : ℝ) ^ ((5 : ℝ) / 4) - 7 = 25 := by
    rw [h4]
    all_goals norm_num
  
  have h6 : Real.sqrt ((16 : ℝ) ^ ((5 : ℝ) / 4) - 7) = 5 := by
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  
  rw [h3, h6]
  all_goals norm_num