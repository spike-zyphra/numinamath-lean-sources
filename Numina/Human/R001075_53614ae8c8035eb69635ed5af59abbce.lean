import Mathlib

/- At Annville Junior High School, $30\%$ of the students in the Math Club are in the Science Club, and $80\%$ of the students in the Science Club are in the Math Club. There are 15 students in the Science Club. How many students are in the Math Club? -/
theorem algebra_20331 {math_club science_club : ℕ}
    (h1 : (math_club * 30 / 100 : ℝ) = science_club * 80 / 100)
    (h2 : science_club = 15) :
    math_club = 40 := by 
  field_simp at h1
  norm_cast at h1
  linarith