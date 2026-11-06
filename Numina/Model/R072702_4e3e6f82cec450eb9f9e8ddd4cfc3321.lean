import Mathlib

theorem algebra_16990 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a = 3 * b) (h' : 2 * (a + b) = 120) :
    a * b = 675 := by
  have ha_eq : a = 3 * b := h

  rw [ha_eq] at h'

  have hb_val : b = 15 := by
    linarith

  have ha_val : a = 45 := by
    rw [hb_val] at ha_eq
    linarith

  rw [ha_val, hb_val]
  all_goals norm_num