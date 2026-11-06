import Mathlib

theorem algebra_276133 (total_people : ℕ) (h : total_people = 140)
    (average_age : ℝ) (h1 : average_age = 24) (average_age_m : ℝ)
    (h2 : average_age_m = 21) (average_age_f : ℝ) (h3 : average_age_f = 28)
    (females : ℕ) (hf : females ≠ 0) (h4 : (total_people - females) * average_age_m + females * average_age_f = total_people * average_age) :
    females = 60 := by 
  rw [h] at h4
  rw [h1] at h4
  rw [h2] at h4
  rw [h3] at h4
  have h5 : (females : ℝ) = 60 := by 
    norm_num at h4 ⊢
    have h6 : (females : ℝ) = 60 := by 
      linarith 
    exact h6
  have h7 : females = 60 := by 
    exact_mod_cast h5
  exact h7