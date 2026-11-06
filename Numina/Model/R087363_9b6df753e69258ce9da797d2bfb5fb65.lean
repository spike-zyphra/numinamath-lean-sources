import Mathlib

theorem algebra_253591 (x : ℝ) (h : Real.sin x = 3 * Real.cos x) : Real.sin x * Real.cos x = 3 / 10 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [show Real.sin x ^ 2 = (3 * Real.cos x) ^ 2 by rw [h]] at h1
  have h2 : 9 * Real.cos x ^ 2 + Real.cos x ^ 2 = 1 := by
    linarith
  have h3 : Real.cos x ^ 2 = 1 / 10 := by 
    linarith
  have h4 : Real.sin x * Real.cos x = 3 * Real.cos x ^ 2 := by
    rw [show Real.sin x = 3 * Real.cos x by linarith]
    all_goals ring
  rw [h4]
  rw [h3]
  all_goals norm_num
  all_goals nlinarith
  all_goals linarith
  all_goals norm_num
  all_goals linarith
  all_goals nlinarith
  all_goals nlinarith