import Mathlib

/- In Mrs. Marsh's algebra class, 30 of the 36 students took the Chapter 4 test, and their mean score was $72 \%$. The next day the other six students took the test and their mean score was $78 \%$. What is the new class mean? Express your answer as a percent. -/
theorem algebra_10900 (total_students : ℕ) (h : total_students = 36)
    (students_tested : ℕ) (h_students_tested : students_tested = 30)
    (mean_score_tested : ℝ) (h_mean_score_tested : mean_score_tested = 72 / 100)
    (students_not_tested : ℕ) (h_students_not_tested : students_not_tested = 6)
    (mean_score_not_tested : ℝ) (h_mean_score_not_tested : mean_score_not_tested = 78 / 100) :
    (students_tested * mean_score_tested + students_not_tested * mean_score_not_tested) / total_students = 73 / 100 := by
  norm_num [h, h_students_tested, h_mean_score_tested, h_students_not_tested, h_mean_score_not_tested]