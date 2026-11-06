import Mathlib

theorem algebra_206033 (M : ℝ) (hM : M > 0) (h : (1 - 1 / 5) * (1 - 1 / 5) * (1 - 1 / 5) * M = (1 - 1 / 5) * (1 - 1 / 5) * (1 - 1 / 5) * (M - 1) + 1.5) :
    M = 1.75 := by 
  norm_num at h ⊢
  all_goals linarith