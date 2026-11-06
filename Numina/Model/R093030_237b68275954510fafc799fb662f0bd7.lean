import Mathlib

theorem algebra_19954 (total_students : ℕ) (h : total_students = 50)
    (students_in_h : ℕ) (students_in_b : ℕ) (students_in_neither : ℕ)
    (h1 : students_in_h = 33) (h2 : students_in_b = 24) (h3 : students_in_neither = 8) :
    students_in_h + students_in_b - total_students + students_in_neither = 15 := by 
  calc 
    students_in_h + students_in_b - total_students + students_in_neither = 33 + 24 - 50 + 8 := by 
      rw [h1, h2, h, h3]
    _ = 15 := by 
      norm_num