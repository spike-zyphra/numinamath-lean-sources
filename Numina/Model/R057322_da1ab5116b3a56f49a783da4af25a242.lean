import Mathlib

theorem algebra_168978 (v : ℝ) (h : v > 0) (h1 : 1.4 * v * (11.22 - 11.08) = v * (11.22 - 11.08) + v * (11.08 - 10.33)) :
    11.22 - 11.08 = 10.33 - 11.08 := by
  norm_num at h1
  nlinarith