import Mathlib

theorem algebra_221739 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : y = x + 3) (h2 : z = x - 2) (h3 : 1 / x + 1 / y + 1 / z = 1 / 4) :
    x = 12 := by
  rw [show y = x + 3 by linarith] at h3
  rw [show z = x - 2 by linarith] at h3
  have h4 : x - 2 > 0 := by
    by_contra h
    push_neg at h
    have h5 : z ≤ 0 := by
      nlinarith [h2, h]
    nlinarith
  have hx1 : x + 3 > 0 := by
    nlinarith
  field_simp [(show x ≠ 0 by linarith), (show x + 3 ≠ 0 by nlinarith), (show x - 2 ≠ 0 by nlinarith)] at h3
  have h5 : x^3 - 11 * x^2 - 14 * x + 24 = 0 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos (show (0 : ℝ) < x + 3 by nlinarith), sq_pos_of_pos (show (0 : ℝ) < x - 2 by nlinarith)]
  have h6 : (x - 12) * (x^2 + x - 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case x - 12 = 0, so x = 12
    linarith
  · -- Case x^2 + x - 2 = 0, so factored
    have h9 : (x - 1) * (x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h9 h9
    · -- Case x - 1 = 0, so x = 1
      nlinarith [show x - 2 > 0 from h4]
    · -- Case x + 2 = 0, so x = -2
      nlinarith [show x > 0 from hx]