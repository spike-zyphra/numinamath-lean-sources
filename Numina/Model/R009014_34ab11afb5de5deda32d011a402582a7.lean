import Mathlib

theorem algebra_9084 (a b c : ℝ) (ha : a = 1) (hb : b = -4) (hc : c = 3) : discrim a b c = 4 := by
  rw [discrim]
  rw [ha, hb, hc]
  norm_num