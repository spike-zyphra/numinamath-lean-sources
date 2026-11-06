import Mathlib

theorem algebra_327756 {a : ℝ} (ha : 0 < a) (h : (100 + a) * 0.02 = 100 * 0.03) :
    (100 + 2 * a) * 0.015 = 100 * 0.03 := by
  have ha2 : a = 50 := by
    norm_num at h
    nlinarith
  rw [ha2]
  norm_num