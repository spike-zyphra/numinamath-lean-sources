import Mathlib

theorem inequalities_598971 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    a / (a^2 + 4) + b / (b^2 + 4) + c / (c^2 + 4) ≤ 3 / 5 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : a / (a^2 + 4) + b / (b^2 + 4) + c / (c^2 + 4) - 3 / 5 ≤ 0 := by
    have pos1 : 0 < (a^2 + 4) * (b^2 + 4) * (c^2 + 4) := by
      positivity
    have h3 : a / (a^2 + 4) + b / (b^2 + 4) + c / (c^2 + 4) - 3 / 5 =
        (5 * a * (b^2 + 4) * (c^2 + 4) + 5 * b * (a^2 + 4) * (c^2 + 4) + 5 * c * (a^2 + 4) * (b^2 + 4) - 3 * (a^2 + 4) * (b^2 + 4) * (c^2 + 4)) / (5 * (a^2 + 4) * (b^2 + 4) * (c^2 + 4)) := by
      field_simp
      ring
    rw [h3]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- Show that the denominator is non-negative
      positivity
  linarith