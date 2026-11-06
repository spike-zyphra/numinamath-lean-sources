import Mathlib

theorem algebra_281730 (total_students : ℕ) (h : total_students = 30)
    (avg_height : ℝ) (h1 : avg_height = 140) (num_boys : ℕ) (h2 : num_boys = 18)
    (avg_height_boys : ℝ) (h3 : avg_height_boys = 144) (num_girls : ℕ) (avg_height_girls : ℝ) (h4 : num_girls = total_students - num_boys) (h5 : num_girls * avg_height_girls + num_boys * 144 = total_students * 140):
     avg_height_girls = 134 := by
  have h6 : num_girls = 12 := by 
    simp [h4, h, h2]
  have eq1 : (↑num_girls : ℝ) = 12 := by
    exact_mod_cast h6
  have eq2 : (↑num_boys : ℝ) = 18 := by
    exact_mod_cast h2
  have eq3 : (↑total_students : ℝ) = 30 := by
    exact_mod_cast h
  norm_num [eq1, eq2, eq3, h3, h1] at h5 ⊢
  linarith