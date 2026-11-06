import Mathlib

theorem algebra_12932 (P : ℝ) (hP : P = 10000) (r : ℝ) (hr : r > 0)
    (h : (P * (1 + 12 / 100 / 2) * (1 + r / 100 / 2)) = 11130) :
    r = 10 := by
  rw [hP] at h
  norm_num at h
  linarith