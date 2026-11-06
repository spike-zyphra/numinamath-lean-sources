import Mathlib

theorem algebra_21648 {r : ℝ} (hr : r ^ 2 + 5 * r + 7 = 0) :
    (r - 1) * (r + 2) * (r + 6) * (r + 3) = 13 := by
  have h1 : r^2 + 5 * r = -7 := by linarith
  calc 
    (r - 1) * (r + 2) * (r + 6) * (r + 3)
        = ((r - 1) * (r + 6)) * ((r + 2) * (r + 3)) := by ring_nf
    _ = (r^2 + 5 * r - 6) * (r^2 + 5 * r + 6) := by 
        nlinarith 
    _ = (-7 - 6) * (-7 + 6) := by 
      rw [h1]
      all_goals linarith 
    _ = ( -13 ) * (-1) := by
      norm_num
    _ = 13 := by 
      norm_num