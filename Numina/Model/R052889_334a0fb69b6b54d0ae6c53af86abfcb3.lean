import Mathlib

theorem algebra_206967 (x : ℝ) (hx : x ≠ 0) (h : (1 + 1200 / x) * (1 - 11 / 100) * x = x - 32) :
    x = 10000 := by
  field_simp [hx] at h
  ring_nf at h
  have h2 : (x - 10000) * x = 0 := by
    nlinarith [sq_pos_of_ne_zero hx]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · linarith
  · have : x = 0 := by linarith
    contradiction