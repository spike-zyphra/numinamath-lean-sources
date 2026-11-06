import Mathlib

theorem algebra_282594 (P : ℝ) (r : ℝ) (t : ℝ) (hP : P = 23904) (hr : r = 0.05) (ht : t = 1)
    (h : 58 * P = 100 * r * t) :
    P * (1 + r * t) = 1400000 := by
  rw [hP, hr, ht] at h 
  norm_num at h 
  all_goals 
    linarith