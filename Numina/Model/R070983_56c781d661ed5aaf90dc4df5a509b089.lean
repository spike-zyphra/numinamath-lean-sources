import Mathlib

theorem algebra_282320 (total_people : ℕ) (h : total_people = 60)
    (average_score : ℝ) (h1 : average_score = 80) (male_average : ℝ)
    (hm : male_average = 83) (female_average : ℝ) (hf : female_average = 78)
    (male_workers : ℕ) (female_workers : ℕ) (h2 : male_workers + female_workers = total_people)
    (h3 : (male_workers * male_average + female_workers * female_average) / total_people = average_score) :
    female_workers = 36 := by
  rw [h] at h2 h3
  rw [h1] at h3
  rw [hm] at h3
  rw [hf] at h3
  have eq1 : (male_workers : ℝ) + (female_workers : ℝ) = (60 : ℝ) := by
    exact_mod_cast h2
  have eq2 : ((male_workers : ℝ) * (83 : ℝ) + (female_workers : ℝ) * (78 : ℝ) ) / (60 : ℝ) = (80 : ℝ) := by
    norm_num at h3 ⊢
    exact_mod_cast h3
  have eq3 : (male_workers : ℝ) * (83 : ℝ) + (female_workers : ℝ) * (78 : ℝ) = (80 : ℝ) * (60 : ℝ) := by
    linarith [eq2]
  have eq4 : (male_workers : ℝ) = (60 : ℝ) - (female_workers : ℝ) := by linarith [eq1]
  rw [eq4] at eq3
  ring_nf at eq3
  have hf : (female_workers : ℝ) = 36 := by
    linarith
  have h4 : female_workers = 36 := by
    exact_mod_cast hf
  exact h4