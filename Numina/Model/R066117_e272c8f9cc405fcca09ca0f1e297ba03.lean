import Mathlib

theorem algebra_94872 (d : ℝ) (h : d ≠ 0) (h1 : 60 = 3 * d) : 100 = 5 * d := by
  have hd : d = 20 := by 
    linarith 
  rw [hd]
  all_goals norm_num