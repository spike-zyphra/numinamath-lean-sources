import Mathlib

theorem algebra_176806 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : v1 * 60 = v2 * (60 - 5)) (h2 : v1 * 60 = v2 * 120) :
    v1 = 3 ∧ v2 = 5 := by 
  norm_num at h1 h2
  have h2' : v2 = 0 := by
    nlinarith
  linarith