import Mathlib

theorem algebra_193758 (a b : ℝ) (ha : a = 1 / 5) (hb : b = 1 / 7) :
    1 / (a + b) * 60 = 175 := by
  rw [ha, hb]
  norm_num