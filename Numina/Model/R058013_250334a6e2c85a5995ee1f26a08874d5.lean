import Mathlib

theorem algebra_227818 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : 16 / v1 = 4 / v2) (h2 : 16 * (v1 - v2) = 4 * (v1 + v2) - 64) :
    v1 = 20 := by
  have h3 : v1 ≠ 0 := by linarith
  have h4 : v2 ≠ 0 := by linarith
  field_simp [h3, h4] at h1
  ring_nf at h1
  -- get the relation v1 = 4 * v2
  have h5 : v1 = 4 * v2 := by
    nlinarith
  rw [h5] at h2
  -- substituting into h2 leads to contradiction.
  nlinarith