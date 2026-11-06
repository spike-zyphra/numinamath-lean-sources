import Mathlib

theorem algebra_317246 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hne : ¬(a = b ∧ b = c)) :
    ∃ x y z, x = (a + b + c)^2 - 9 * a * b ∧ y = (a + b + c)^2 - 9 * b * c ∧
    z = (a + b + c)^2 - 9 * c * a ∧ (x > 0 ∨ y > 0 ∨ z > 0) := by
  use (a + b + c) ^ 2 - 9 * a * b, (a + b + c) ^ 2 - 9 * b * c, (a + b + c) ^ 2 - 9 * c * a
  constructor
  · -- Show the first equality
    rfl
  constructor
  · -- Show the second equality
    rfl
  constructor
  · -- Show the third equality
    rfl
  by_contra h
  push_neg at h
  have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 > 0 := by
    have h2 : (a - b) ^ 2 > 0 := by
      by_contra h
      push_neg at h
      have : a = b := by nlinarith
      have h3 : b = c := by
        nlinarith [show (b - c) ^ 2 > 0 by
          by_contra h
          push_neg at h
          have : b = c := by nlinarith
          have h1 : a = b := by linarith
          have h2 : b = c := by linarith
          tauto
        ]
      have h1 : a = b := by linarith
      have h2 : b = c := by linarith
      tauto
    nlinarith [sq_nonneg (a - c), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c), sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a + c - b),
          sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, 
          h1]