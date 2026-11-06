import Mathlib

theorem algebra_198090 {a b : ℝ} (ha : 10 * a ^ 2 - 3 * b ^ 2 + 5 * a * b = 0) (hb : 9 * a ^ 2 - b ^ 2 ≠ 0) :
    (2 * a - b) / (3 * a - b) + (5 * b - a) / (3 * a + b) = -3 := by
  have h1 : 3 * a - b ≠ 0 := by
    by_contra h
    have h2 : 3 * a = b := by linarith
    have h3 : 9 * a ^ 2 - b ^ 2 = 0 := by
      rw [show b = 3 * a by linarith]
      ring_nf
    contradiction
  have h4 : 3 * a + b ≠ 0 := by
    by_contra h
    have h5 : b = -3 * a := by linarith
    have h6 : 9 * a ^ 2 - b ^ 2 = 0 := by
      rw [show b = -3 * a by linarith]
      ring_nf
    contradiction
  field_simp [h1, h4]
  -- need to manipulate the expressions to get numerator and denominator
  nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (3 * a), sq_nonneg (b), sq_pos_of_ne_zero (show 9 * a ^ 2 - b ^ 2 ≠ 0 by assumption)]