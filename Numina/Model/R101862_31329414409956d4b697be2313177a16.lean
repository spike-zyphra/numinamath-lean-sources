import Mathlib

theorem algebra_93452 (t : ℝ) (ht : t > 0) (h : 10 + 11 * t = 10 + 8 * t + 17 * (t - 2) ∧
    10 + 8 * t + 17 * (t - 2) = 10 + 15 * t) :
    t = 5.5 := by
  linarith