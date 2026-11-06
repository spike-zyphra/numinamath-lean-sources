import Mathlib

theorem algebra_234187 (l w : ℝ) (hl : l > 0) (hw : w > 0)
    (h : (1 - 1 / 18) * l * (1 - 1 / 14) * w = 221) (h' : w = 875 / 1000) :
    l = 288 := by 
  rw [h'] at h
  norm_num at h 
  linarith