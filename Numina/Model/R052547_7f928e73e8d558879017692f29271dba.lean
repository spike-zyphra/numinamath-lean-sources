import Mathlib

theorem algebra_127176 (T : ℝ) (h : T > 0) (h1 : (45 - T) / (45 - 5) = (77 - T) / (77 - 45)) :
    T = 205 := by
  norm_num at h1
  linarith