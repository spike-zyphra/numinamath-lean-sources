import Mathlib

theorem algebra_287927 (d v1 v2 v3 : ℝ) (h1 : d > 0) (h2 : v1 > 0) (h3 : v2 > 0) (h4 : v3 > 0)
    (h5 : v1 = 3 * v2) (h6 : v1 = 5 * v3) (h7 : d / v2 = 6) :
    d / v3 = 10 := by
  have h8 : d = 6 * v2 := by
    have h9 : v2 ≠ 0 := by linarith
    field_simp [h9] at h7
    linarith
  have h9 : 3 * v2 = 5 * v3 := by 
    linarith [h5, h6]
  have h10 : v2 = (5 / 3) * v3 := by
    linarith
  have h11 : d = 10 * v3 := by
    rw [h8]
    rw [h10]
    ring
  have h12 : v3 ≠ 0 := by linarith
  field_simp [h12]
  linarith [h11]