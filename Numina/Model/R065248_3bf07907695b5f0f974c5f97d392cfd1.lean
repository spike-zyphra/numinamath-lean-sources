import Mathlib

theorem algebra_262010 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : v1 / v2 = 5 / 4) (h2 : v1 * v2 = 20 * 4) (h3 : v1 * (v2 - v1) = 75 * 3) :
    v2 = 10 := by
  have h4 : v1 = (5 / 4) * v2 := by
    have h5 : v2 ≠ 0 := by linarith
    field_simp at h1
    nlinarith
  have h5 : v2^2 = 64 := by
    rw [show v1 = (5 / 4) * v2 by linarith [h4]] at h2
    nlinarith
  have h6 : v2 = 8 := by
    nlinarith [sq_nonneg (v2 - 8), h']
  have h7 : v1 = 10 := by 
    rw [show v2 = 8 by linarith [h6]] at h4
    nlinarith 
  nlinarith [h3, h6, h7, h, h']