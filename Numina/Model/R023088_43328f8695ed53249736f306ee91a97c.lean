import Mathlib

theorem algebra_10112 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (h : a^3 - b^3 = a^2 - b^2) :
    ∃ c : ℤ, c = 9 * a * b ∧ c = 1 ∨ c = 2 ∨ c = 3 := by
  have h1 : a ^ 3 - b ^ 3 = (a - b) * (a^2 + a * b + b^2) := by
    ring
  have h2 : a^2 - b^2 = (a - b) * (a + b) := by
    ring
  rw [h1, h2] at h
  have h3 : a - b ≠ 0 := by
    intro h'
    apply hab
    linarith
  have h6 : a^2 + a * b + b^2 = a + b := by
    have h7 : (a - b) * (a^2 + a * b + b^2) = (a - b) * (a + b) := by linarith
    have h8 : (a^2 + a * b + b^2) * (a - b) = (a + b) * (a - b) := by 
      rw [show (a - b) * (a^2 + a * b + b^2) = (a^2 + a * b + b^2) * (a - b) by ring] at h7
      rw [show (a - b) * (a + b) = (a + b) * (a - b) by ring] at h7
      linarith
    -- Now using mul_right_inj' to get h5
    have h9 : a ^ 2 + a * b + b ^ 2 = a + b := by
      apply (mul_right_inj' h3).mp
      linarith [h8]
    exact h9
  -- all distinct, rewrite h6 to h10, and where compute the relations.
  have h4 : a * b > 0 := mul_pos ha hb
  have h5 : a + b > 0 := add_pos ha hb
  -- equations for converting between variables
  have h7 : a * b = (a + b) ^ 2 - (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h6]
  have h8 : a + b > 1 := by
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h'
      apply hab
      linarith
    ), sq_nonneg (a - b), sq_nonneg (a + b - 1)]
  have h10 : a * b < 4 / 9 := by
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h'
      apply hab
      linarith
    ), sq_nonneg (a + b - 4 / 3), sq_nonneg (a - b), sq_nonneg (a), sq_nonneg (b)]
  have h9 : 9 * a * b > 0 := by
    nlinarith
  have h11 : 9 * a * b < 4 := by
    nlinarith
  use 2
  simp