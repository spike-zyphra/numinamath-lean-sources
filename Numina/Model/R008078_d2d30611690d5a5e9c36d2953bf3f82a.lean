import Mathlib

theorem algebra_15061 (a b c : ℝ) (h : a = 3) (hb : b = 3 + 1 / 3) (hc : c = 1 / 3) :
    discrim a b c = 64 / 9 := by
  rw [discrim]
  rw [h, hb, hc]
  norm_num