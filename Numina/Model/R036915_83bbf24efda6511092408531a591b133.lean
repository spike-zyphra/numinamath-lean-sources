import Mathlib

open Real

theorem algebra_290556 : ∑ i ∈ Finset.range 10, logb 3 ((1 : ℝ) - 1 / (15 - i)) = -1 := by
  norm_num [Finset.sum_range_succ]
  have h1 : logb 3 ((14 / 15 : ℝ)) + logb 3 ((13 / 14 : ℝ)) + logb 3 ((12 / 13 : ℝ)) + logb 3 ((11 / 12 : ℝ)) + logb 3 ((10 / 11 : ℝ)) + logb 3 ((9 / 10 : ℝ)) + logb 3 ((8 / 9 : ℝ)) + logb 3 ((7 / 8 : ℝ)) + logb 3 ((6 / 7 : ℝ)) + logb 3 ((5 / 6 : ℝ)) = -1 := by 
    have h2 : logb 3 ((14 / 15 : ℝ)) + logb 3 ((13 / 14 : ℝ)) + logb 3 ((12 / 13 : ℝ)) + logb 3 ((11 / 12 : ℝ)) + logb 3 ((10 / 11 : ℝ)) + logb 3 ((9 / 10 : ℝ)) + logb 3 ((8 / 9 : ℝ)) + logb 3 ((7 / 8 : ℝ)) + logb 3 ((6 / 7 : ℝ)) + logb 3 ((5 / 6 : ℝ)) = logb 3 ((14 / 15 : ℝ) * (13 / 14 : ℝ) * (12 / 13 : ℝ) * (11 / 12 : ℝ) * (10 / 11 : ℝ) * (9 / 10 : ℝ) * (8 / 9 : ℝ) * (7 / 8 : ℝ) * (6 / 7 : ℝ) * (5 / 6 : ℝ)) := by 
      rw [← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num), 
          ← logb_mul (by norm_num) (by norm_num)]
    rw [h2]
    have h3 : (14 / 15 : ℝ) * (13 / 14 : ℝ) * (12 / 13 : ℝ) * (11 / 12 : ℝ) * (10 / 11 : ℝ) * (9 / 10 : ℝ) * (8 / 9 : ℝ) * (7 / 8 : ℝ) * (6 / 7 : ℝ) * (5 / 6 : ℝ) = (1 / 3 : ℝ) := by 
      norm_num
    rw [h3]
    have h4 : logb 3 ((1 / 3 : ℝ)) = -1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h4]
  linarith [h1]