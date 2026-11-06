import Mathlib

theorem algebra_132154 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a = b + 3) (h' : a * 20 = 2 * b * 15) :
    a * 20 + b * 15 = 270 := by
  have hb_eq : b = 6 := by
    rw [h] at h'
    linarith
  have ha_eq : a = 9 := by
    rw [hb_eq] at h
    linarith
  rw [ha_eq, hb_eq]
  norm_num