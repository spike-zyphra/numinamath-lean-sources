import Mathlib

theorem algebra_97792 (total_distance : ℝ) (total_time : ℝ)
    (h : total_distance = 80 + 100) (h' : total_time = 1.5 + 0.5 + 2) :
    total_distance / total_time = 45 := by
  rw [h, h']
  norm_num