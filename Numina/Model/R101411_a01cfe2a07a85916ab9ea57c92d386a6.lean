import Mathlib

theorem algebra_13951 {a b : ℤ} (ha : a = -3) (hb : b = 2) : -a - b^3 + a * b = -11 := by
  rw [ha, hb]
  norm_num