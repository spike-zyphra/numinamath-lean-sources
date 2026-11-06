import Mathlib

theorem algebra_7577 (total_students : ℕ) (h : total_students = 30)
    (average_time : ℝ) (h1 : average_time = 21) (male_students : ℕ)
    (hm : male_students * 25 + (total_students - male_students) * 19 = total_students * average_time) :
    male_students = 10 := by
  have h2 : (total_students : ℝ) = 30 := by
    exact_mod_cast h
  have h3 : (average_time : ℝ) = 21 := by 
    exact_mod_cast h1
  have eq1 : (male_students : ℝ) * 25 + ((total_students : ℝ) - (male_students : ℝ)) * 19 = (total_students : ℝ) * (average_time : ℝ) := by
    exact_mod_cast hm
  rw [h2, h3] at eq1
  have h4 : (male_students : ℝ) = 10 := by
    norm_num at eq1 
    linarith 
  exact_mod_cast h4