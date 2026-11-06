import Mathlib

theorem algebra_11252 {a b c d : ℝ} (ha : a = 24) (hb : b = 10) :
    (1/2) * a * b = 120 := by
  rw [ha, hb]
  norm_num