import Mathlib

theorem algebra_12121 (total_students : ℕ) (h : total_students = 300) (students_wwho_who_cats : ℕ)
    (h2 : students_who_who_cats = 30) :
    (students_who_who_cats * 100 : ℝ) / total_students = 10 := by
  rw [h, h2]
  all_goals norm_num
  <;> norm_num