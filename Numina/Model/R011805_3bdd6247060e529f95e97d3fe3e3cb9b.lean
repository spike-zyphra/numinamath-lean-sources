import Mathlib

theorem algebra_152191 {a b c : ℝ} (ha : a ≠ 0) (h1 : a + b + c = a * b * c) (h2 : a ^ 2 = b * c) :
    3 ≤ a ^ 2 := by

  have h3 : a + b + c = a ^ 3 := by
    have h4 : a * b * c = a ^ 3 := by
      calc
        a * b * c = a * (b * c) := by ring
        _ = a * (a ^ 2) := by rw [show b * c = a ^ 2 by nlinarith [h2]]
        _ = a ^ 3 := by ring
    linarith [h1, h4]

  have h4 : b + c = a ^ 3 - a := by
    linarith [h3]

  have h6 : (b + c) ^ 2 - 4 * a ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 2 * a), sq_nonneg (a ^ 2 - 3), sq_pos_of_ne_zero (show a ^ 2 ≠ 0 by
      intro h'
      apply ha
      nlinarith
    ), sq_nonneg (a ^ 2), h2, h4]

  have h7 : (a ^ 3 - a) ^ 2 - 4 * a ^ 2 ≥ 0 := by
    rw [show (b + c) = a ^ 3 - a by linarith [h4]] at h6
    linarith

  have h9 : a ^ 4 - 2 * a ^ 2 - 3 ≥ 0 := by
    have ha2_pos : a ^ 2 > 0 := by
      have ha' : a ≠ 0 := ha
      have : a ^ 2 > 0 := by
        exact sq_pos_of_ne_zero ha'
      linarith
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a ^ 3 - a - 2 * a), sq_nonneg (a ^ 3 + a), sq_nonneg (a ^ 2 - 3), sq_pos_of_ne_zero (show a ^ 2 ≠ 0 by
      intro h'
      apply ha
      nlinarith
    ), sq_nonneg (a ^ 4 - 2 * a ^ 2)]

  have h10 : a ^ 2 ≥ 3 := by
    nlinarith [sq_nonneg (a ^ 2 - 3), sq_nonneg (a ^ 4 - 2 * a ^ 2 - 3), sq_nonneg (a ^ 2), sq_nonneg (a ^ 4)]

  linarith [h10]