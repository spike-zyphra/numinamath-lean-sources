import Mathlib

theorem algebra_204108 (v1 v2 v3 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0) (h3 : v3 > 0)
    (h4 : v2 = 1.5 * v1) (h5 : v3 = 0.5 * v1) (h6 : 5 / v1 = 30 / v3) :
    (30 - 5) / v3 = 28 := by
  have h7 : v3 ≠ 0 := by nlinarith
  have h8 : v1 ≠ 0 := by nlinarith
  have h7' : 5 * v3 = 30 * v1 := by
    field_simp [h7, h8] at h6
    linarith
  rw [show v3 = 0.5 * v1 by linarith [h5]] at h7'
  ring_nf at h7'
  have h8' : v1 = 0 := by 
    nlinarith
  nlinarith