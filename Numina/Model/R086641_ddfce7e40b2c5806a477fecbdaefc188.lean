import Mathlib

theorem algebra_178262 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x = y + 3) (h2 : 1 / x + 1 / y = 3 / 20) :
    x = 15 := by
  have eq1 : 1 / x + 1 / y = 3 / 20 := h2
  have eq2 : x = y + 3 := h1
  rw [eq2] at eq1
  have h3 : y > 0 := hy
  have h4 : y + 3 > 0 := by
    nlinarith
  field_simp [(show y ≠ 0 by linarith), (show y + 3 ≠ 0 by linarith)] at eq1
  ring_nf at eq1
  have h5 : 3 * y ^ 2 - 31 * y - 60 = 0 := by
    nlinarith
  have h6 : 3 * y ^ 2 - 31 * y - 60 = 0 := h5
  have h7 : 3 * y ^ 2 - 31 * y - 60 = (y - 12) * (3 * y + 5) := by
    ring
  rw [h7] at h6
  cases' (mul_eq_zero.mp h6) with h8 h9
  · -- y - 12 = 0
    have : y = 12 := by linarith
    linarith [eq2, this]
  · -- 3y + 5 = 0
    have : 3 * y + 5 = 0 := by
      linarith
    nlinarith