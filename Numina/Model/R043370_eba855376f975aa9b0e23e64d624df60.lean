import Mathlib

theorem algebra_108573 (a b c : ℝ) (ha : a ≠ -1) (hb : b ≠ -1) (hc : c ≠ -1)
    (habc : a * b * c = 1) (h : 1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1) = 3 / 2) :
    a = 1 ∨ b = 1 ∨ c = 1 := by

  have h1 : a + 1 ≠ 0 := by
    intro h1
    apply ha
    linarith

  have h2 : b + 1 ≠ 0 := by
    intro h2
    apply hb
    linarith

  have h3 : c + 1 ≠ 0 := by
    intro h3
    apply hc
    linarith

  field_simp [h1, h2, h3] at h

  have h4 : (a - 1) * (b - 1) * (c - 1) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (a + 1) ≠ 0 by exact h1), sq_pos_of_ne_zero (show (b + 1) ≠ 0 by exact h2), sq_pos_of_ne_zero (show (c + 1) ≠ 0 by exact h3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

  cases' (mul_eq_zero.mp h4) with h5 h6
  cases' (mul_eq_zero.mp h5) with h7 h8

  · -- h7: $a - 1 = 0$
    left
    linarith

  · -- h8: $b - 1 = 0$
    right
    left
    linarith

  · -- h6: $c - 1 = 0$
    right
    right
    linarith