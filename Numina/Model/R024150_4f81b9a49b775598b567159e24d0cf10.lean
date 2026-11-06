import Mathlib

theorem inequalities_277022 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    b * c / a + a * c / b + a * b / c > a + b + c := by

  have h1 : 0 < a * b * c := by positivity
  have h2 : b * c / a + a * c / b + a * b / c - (a + b + c) > 0 := by

    have h3 : b * c / a + a * c / b + a * b / c - (a + b + c) = (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - (a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp
      ring
    rw [h3] at *
    apply div_pos
    -- Show the numerator is positive
    · -- Show b^2 * c^2 + a^2 * c^2 + a^2 * b^2 > (a + b + c) * (a * b * c)
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
        intro h
        apply hne.left
        linarith
      ), sq_pos_of_ne_zero (show b - c ≠ 0 by
        intro h
        apply hne.right.left
        linarith
      ), sq_pos_of_ne_zero (show a - c ≠ 0 by
        intro h
        apply hne.right.right
        linarith
      ), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    -- Show the denominator is positive
    · -- a * b * c > 0
      positivity
  linarith only [h2]