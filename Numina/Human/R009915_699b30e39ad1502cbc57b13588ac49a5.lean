import Mathlib

/- Makarla attended two meetings during her
9-hour work day. The first meeting took 45 minutes and the second meeting took twice as long.
What percent of her work day was spent attending meetings?
(A) 15
(B) 20
(C) 25
(D) 30
(E) 35
-/

theorem algebra_94195 (total_time : ℝ) (h : total_time = 9 * 60) (first_meeting : ℝ)
(second_meeting : ℝ) (hf : first_meeting = 45) (hs : second_meeting = 2 * first_meeting) :
(first_meeting + second_meeting) / total_time * 100 = 25 := by
  -- First we need determine total time in minutes
  norm_num at h
  -- Then we show total time in meetings is 135 minutes
  have total_meeting_time : first_meeting + second_meeting = 135 := by
    rw [hs, hf]
    norm_num
  -- Bring it together and calculate
  rw [total_meeting_time, h]
  norm_num