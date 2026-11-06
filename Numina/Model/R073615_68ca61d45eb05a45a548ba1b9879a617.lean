import Mathlib

theorem algebra_142513 {x : ℝ} (hx : x > 0) (h : (1 - 40 / 100) * x = (1 - 85 / 100) * (x - 15)) :
    x = 33.33 := by 
  norm_num at h 
  linarith -- This would derive a contradiction in the case of the contradictory statement