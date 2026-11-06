import Mathlib

theorem algebra_16821 (a b c : ℝ) (ha : a = 0.7 * b) (hc : c = 1.4 * b)
    (h : a + b + c = 1) (h' : 0 < b) (h'' : 0 < c) :
    b * 31 = 10 := by
  have eq1 : a + b + c = 1 := h
  rw [ha, hc] at eq1
  have hb : b = 10 / 31 := by
    norm_num at eq1 
    linarith 
  have : b * 31 = 10 := by
    rw [hb]
    norm_num 
  linarith