import Mathlib

theorem algebra_907 (d t : ℝ) (h1 : 0 < d) (h2 : 0 < t) (h3 : d / (16 + 4) = t - 3) (h4 : d / (16 - 4) = t + 3) (h5 : d - 80 = 4 * (t + 3)) :
    d = 120 ∨ d = 200 ∨ d = 100 := by 
  norm_num at h3 h4 h5
  have h6 : d = 20 * (t - 3) := by 
    linarith
  have h7 : d = 12 * (t + 3) := by
    linarith
  have h8 : t = 12 := by 
    nlinarith [h6, h7]
  have h9 : d = 180 := by 
    rw [h8] at h6
    linarith
  rw [h9, h8] at h5
  linarith