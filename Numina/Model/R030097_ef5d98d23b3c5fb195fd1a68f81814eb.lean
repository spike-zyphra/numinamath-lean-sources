import Mathlib

theorem inequalities_55631 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 ≤ (a + 3) / (a + 1) ^ 2 + (b + 3) / (b + 1) ^ 2 + (c + 3) / (c + 1) ^ 2 := by

  have h2 : (a + 3) / (a + 1) ^ 2 + (b + 3) / (b + 1) ^ 2 + (c + 3) / (c + 1) ^ 2 - 3 ≥ 0 := by
    have h4 : (a + 3) / (a + 1) ^ 2 + (b + 3) / (b + 1) ^ 2 + (c + 3) / (c + 1) ^ 2 - 3 =
        ((a + 3) * (b + 1) ^ 2 * (c + 1) ^ 2 + (b + 3) * (a + 1) ^ 2 * (c + 1) ^ 2 + (c + 3) * (a + 1) ^ 2 * (b + 1) ^ 2 - 3 * (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) / ((a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    -- Show that the numerator is non-negative
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    -- Show that the denominator is positive
    positivity
  linarith