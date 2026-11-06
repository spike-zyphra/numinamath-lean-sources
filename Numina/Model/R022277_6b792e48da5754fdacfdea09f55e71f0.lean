import Mathlib

theorem algebra_4440 (l t : ℝ) (hl : l = 400) (ht1 : t = 10) (ht2 : t + 0.1 = 9) :
    l + t * 0.1 = 860 := by
  rw [ht1] at ht2
  norm_num at ht2
  all_goals
    nlinarith