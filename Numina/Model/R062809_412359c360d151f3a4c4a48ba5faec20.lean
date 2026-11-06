import Mathlib

open Real

theorem algebra_2389 {a b c : ℝ}
    (ha : a = abs (-5) / sqrt ((-5)^2)) (hb : b = sqrt ((1 - 3)^2) / (1 - 3))
    (hc : c = abs (4 - 3 / 4) / (3 + 1 / 4)) :
    a = c ∧ c > b := by
  have ha1 : a = 1 := by
    rw [ha]
    have h1 : abs (-5 : ℝ) = 5 := by 
      norm_num [abs_of_nonneg]
    have h2 : sqrt ((-5 : ℝ) ^ 2) = 5 := by 
      rw [Real.sqrt_sq_eq_abs]
      norm_num [abs_of_nonneg]
    rw [h1, h2]
    all_goals norm_num
  have hc1 : c = 1 := by 
    rw [hc]
    norm_num [abs_of_nonneg]
    all_goals norm_num [abs_of_nonneg]
  have hb1 : b = -1 := by
    rw [hb]
    have h3 : sqrt ((1 - 3 : ℝ) ^ 2) = 2 := by 
      rw [Real.sqrt_sq_eq_abs]
      norm_num [abs_of_nonneg]
    rw [h3]
    all_goals norm_num
  constructor
  · -- Show a = c using ha1 and hc1
    rw [ha1, hc1]
  · -- Show c > b using hc1 and hb1
    rw [hc1, hb1]
    all_goals norm_num