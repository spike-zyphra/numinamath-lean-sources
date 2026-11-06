import Mathlib

theorem algebra_163110 (total_length : ℝ) (h : total_length = 3200) (m : ℝ) (hm : m = 2) (s : ℝ)
    (hs : s = 65) :
    total_length * m * s = 416000 := by
  rw [h, hm, hs]
  norm_num