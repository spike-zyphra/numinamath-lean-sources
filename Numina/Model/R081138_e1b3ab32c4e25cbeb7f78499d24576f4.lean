import Mathlib

theorem other_285766 (total_students : ℕ) (h : total_students = 100) (num_girls : ℕ)
    (h_num_girls : num_girls = 40) :
    (num_girls * 100 : ℝ) / total_students = 40 := by
  rw [h, h_num_girls]
  norm_num