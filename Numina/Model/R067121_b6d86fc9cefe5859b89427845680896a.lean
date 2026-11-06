import Mathlib

theorem algebra_165198 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : v1 * 10 = v2 * 5) (h2 : v1 * 400 = v2 * 600) :
    v1 / v2 = 20 := by
  have h3 : v2 = 2 * v1 := by
    linarith
  rw [h3] at h2
  have h4 : v1 = 0 := by
    nlinarith
  linarith