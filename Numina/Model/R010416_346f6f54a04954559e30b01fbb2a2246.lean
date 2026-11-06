import Mathlib

theorem algebra_12992 (t : ℝ) (ht : t > 0) (h : -16 * t ^ 2 + 22 * t + 45 = 0) :
    t = 5 / 2 := by
  have h1 : (2 * t - 5) * (8 * t + 9) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · linarith 
  · linarith