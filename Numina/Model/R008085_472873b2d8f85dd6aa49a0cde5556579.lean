import Mathlib

theorem algebra_13226 (total_people : ℕ) (h : total_people = 40)
    (average_age : ℝ) (h1 : average_age = 17) (num_girls : ℕ) (h2 : num_girls = 20)
    (num_boys : ℕ) (h3 : num_boys = 15) (num_adults : ℕ) (h4 : num_adults = 5)
    (average_age_girls : ℝ) (h5 : average_age_girls = 15) (average_age_boys : ℝ)
    (h6 : average_age_boys = 16) :
    (total_people * average_age - num_girls * average_age_girls - num_boys * average_age_boys) / num_adults = (28 : ℚ) := by
  norm_num [h, h1, h2, h3, h4, h5, h6]
  <;> ring_nf
  <;> norm_num