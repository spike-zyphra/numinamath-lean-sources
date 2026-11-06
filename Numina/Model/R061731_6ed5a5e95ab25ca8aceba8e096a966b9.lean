import Mathlib

theorem algebra_185805 (v : ℝ) (h : v > 0) (h' : 20 / v = 20 / (v + 10) + 4 / 60) :
    v = 50 := by
  have h1 : v ≠ 0 := by linarith
  have h2 : v + 10 ≠ 0 := by
    nlinarith
  field_simp [h1, h2] at h'
  ring_nf at h'
  have h3 : v ^ 2 + 10 * v - 3000 = 0 := by
    linarith
  have h4 : (v - 50) * (v + 60) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · linarith
  · nlinarith