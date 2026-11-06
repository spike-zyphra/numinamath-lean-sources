import Mathlib

theorem algebra_128723 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a * b = 3 * (2 * (a + b))) (hne : a ≠ b) :
    12 < a ∨ 12 < b := by 
  by_contra h'
  push_neg at h'
  have h1 : a ≤ 12 := by nlinarith
  have h2 : b ≤ 12 := by nlinarith

  nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hne), sq_nonneg (a - b)]