import Mathlib

theorem algebra_287666 (x : ℝ) (hx : x = 1 / 2) :
    ((x ^ ((2 : ℝ) / 3)) * (x ^ ((-1 : ℝ) / 2))) /
    ((x ^ ((2 : ℝ) / 6)) ^ 2 * Real.sqrt x) = 2 := by
  rw [hx]
  have h1 : ((1 / 2 : ℝ) ^ ((2 : ℝ) / 3)) * ((1 / 2 : ℝ) ^ ((-1 : ℝ) / 2)) = (1 / 2 : ℝ) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add]
    norm_num
    all_goals norm_num

  have h2 : ((1 / 2 : ℝ) ^ ((2 : ℝ) / 6)) ^ 2 = (1 / 2 : ℝ) ^ (2 / 3 : ℝ) := by
    have h3 : (1 / 2 : ℝ) ^ ((2 : ℝ) / 6) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) := by
      norm_num
    rw [h3]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num

  have h4 : Real.sqrt ((1 / 2 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]

  have h5 : ((1 / 2 : ℝ) ^ ((2 : ℝ) / 6)) ^ 2 * Real.sqrt ((1 / 2 : ℝ)) = (1 / 2 : ℝ) ^ (7 / 6 : ℝ) := by
    rw [h2, h4]
    rw [← Real.rpow_add]
    norm_num
    all_goals norm_num

  rw [h1, h5]

  have h6 : ( (1 / 2 : ℝ) ^ (1 / 6 : ℝ) ) / ( (1 / 2 : ℝ) ^ (7 / 6 : ℝ) ) = ( (1 / 2 : ℝ) ^ (1 / 6 - 7 / 6 : ℝ) ) := by
    rw [← Real.rpow_sub]
    all_goals norm_num
  rw [h6]

  have h7 : (1 / 6 : ℝ) - (7 / 6 : ℝ) = (-1 : ℝ) := by
    norm_num
  rw [h7]

  norm_num