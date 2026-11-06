import Mathlib

theorem algebra_94195 (total_time : ℝ) (h : total_time = 9 * 60) (first_meeting : ℝ)
(second_meeting : ℝ) (hf : first_meeting = 45) (hs : second_meeting = 2 * first_meeting) :
(first_meeting + second_meeting) / total_time * 100 = 25 := by
  have h1 : second_meeting = 90 := by
    rw [hs, hf]
    norm_num -- This will compute 2 * 45 to get 90
  rw [h] -- This substitutes total_time with 9 * 60 = 540
  rw [hf] -- This substitutes first_meeting with 45
  rw [h1] -- This substitutes second_meeting with 90
  norm_num -- This simplifies the expression to verify it's indeed 25