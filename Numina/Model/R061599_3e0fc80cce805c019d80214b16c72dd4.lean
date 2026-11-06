import Mathlib

theorem algebra_239394 (total_distance : ℝ) (h : total_distance = 150) (first_hour : ℝ)
    (second_hour : ℝ) (third_hour : ℝ) (h_first : first_hour = 4 / 15 * total_distance)
    (h_second : second_hour = 5 / 8 * first_hour) (h_third : third_hour = 2 / 3 * (first_hour + second_hour)) :
    total_distance - (first_hour + second_hour + third_hour) = 41 + 2 / 3 := by
  rw [h] at h_first
  have hf : first_hour = 40 := by 
    linarith
  rw [hf] at h_second
  have hs : second_hour = 25 := by
    linarith
  rw [hs, hf] at h_third
  have ht : third_hour = 130 / 3 := by
    linarith
  rw [h, hf, hs, ht]
  norm_num