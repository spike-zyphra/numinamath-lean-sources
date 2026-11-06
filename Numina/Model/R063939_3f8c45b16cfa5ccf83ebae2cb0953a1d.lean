import Mathlib

theorem algebra_294091 (d v : ℝ) (h : d > 0) (h1 : v > 0) (h2 : d / (v + 1 / 2) = 4 / 5 * d / v)
    (h3 : d / (v - 1 / 2) = d / v + 2.5) : d = 15 := by
  have h4 : d ≠ 0 := by linarith
  have h5 : v + 1 / 2 ≠ 0 := by
    nlinarith
  have h6 : v ≠ 0 := by nlinarith
  have h7 : d * v = 4 / 5 * d * (v + 1 / 2) := by
    field_simp [(show v + 1 / 2 ≠ 0 by linarith), (show v ≠ 0 by linarith)] at h2
    nlinarith
  have h9 : v = 2 := by
    have h8 : d ≠ 0 := by linarith
    apply (mul_left_inj' h8).mp
    linarith
  have eq2 : d / (v - 1 / 2) = d / v + 2.5 := h3
  rw [show v - 1 / 2 = (2 - 1 / 2 : ℝ) by linarith [h9]] at eq2
  rw [show v = (2 : ℝ) by linarith [h9]] at eq2
  norm_num at eq2
  nlinarith