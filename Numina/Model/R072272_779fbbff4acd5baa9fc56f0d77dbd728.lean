import Mathlib

theorem algebra_287873 (d : ℝ) (h : d > 0) (h1 : 100 * d / 90 = 100 * d / 75 + 3) :
    d = 6650 := by
  have eq2 : 7500 * d = 9000 * d + 20250 := by 
    field_simp at h1
    linarith
  have neg_d : d < 0 := by
    linarith
  linarith