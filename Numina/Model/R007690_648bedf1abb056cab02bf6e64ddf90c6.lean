import Mathlib

theorem algebra_10900 (total_students : ℕ) (h : total_students = 36)
    (students_tested : ℕ) (h_students_tested : students_tested = 30)
    (mean_score_tested : ℝ) (h_mean_score_tested : mean_score_tested = 72 / 100)
    (students_not_tested : ℕ) (h_students_not_tested : students_not_tested = 6)
    (mean_score_not_tested : ℝ) (h_mean_score_not_tested : mean_score_not_tested = 78 / 100) :
    (students_tested * mean_score_tested + students_not_tested * mean_score_not_tested) / total_students = 73 / 100 := by
  rw [h] -- total_students = 36
  rw [h_students_tested] -- students_tested = 30
  rw [h_mean_score_tested] -- mean_score_tested = 72/100
  rw [h_students_not_tested] -- students_not_tested = 6
  rw [h_mean_score_not_tested] -- mean_score_not_tested = 78/100
  norm_num