import Mathlib

theorem algebra_275940 (total_students : ℕ) (h : total_students = 45)
    (students_good_english : ℕ) (students_good_chinese : ℕ)
    (students_good_both : ℕ) (h1 : students_good_english = 35) (h2 : students_good_chinese = 31)
    (h3 : students_good_both = 24) :
    total_students - (students_good_english + students_good_chinese - students_good_both) = 3 := by 
  calc
    total_students - (students_good_english + students_good_chinese - students_good_both)
        = 45 - (35 + 31 - 24) := by 
          rw [h, h1, h2, h3]
    _ = 45 - (66 - 24) := by norm_num
    _ = 45 - 42 := by norm_num
    _ = 3 := by norm_num