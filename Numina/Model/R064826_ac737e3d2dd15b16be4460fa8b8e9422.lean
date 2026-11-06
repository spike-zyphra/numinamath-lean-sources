import Mathlib

open Real

theorem algebra_148325 : ¬ logb 4 2 = 2 := by 
  by_contra h
  have h1 : logb 4 2 = (Real.log 2) / (Real.log 4) := by 
    field_simp [logb]
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log (2 ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by simp [Real.log_pow]
  have h3 : Real.log 2 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h4 : logb 4 2 = 1 / 2 := by 
    rw [h1]
    rw [h2]
    field_simp [show Real.log 2 ≠ 0 by linarith]
    all_goals linarith
  rw [h4] at h
  all_goals linarith