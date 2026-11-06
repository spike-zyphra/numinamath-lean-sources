import Mathlib

theorem algebra_236524 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (harea : a * b = 3 * (2 * (a + b))) : 12 < a ∨ 12 < b := by
  by_contra h
  push_neg at h
  have h1 : a ≤ 12 := by linarith
  have h2 : b ≤ 12 := by linarith
  have h3 : a * b = 6 * (a + b) := by 
    linarith
  nlinarith [sq_nonneg (a - 12), sq_nonneg (b - 12), sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
    intro h'
    apply hne
    linarith
  ), mul_pos ha hb
  ]