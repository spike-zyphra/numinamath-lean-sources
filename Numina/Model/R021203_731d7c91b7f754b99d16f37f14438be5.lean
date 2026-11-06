import Mathlib

theorem inequalities_95176 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) +
    (c^3 + 3 * a^3) / (5 * c + a) ≥
    2 / 3 * (a^2 + b^2 + c^2) := by
  have h1 : 0 < (5 * a + b) * (5 * b + c) * (5 * c + a) := by positivity
  have h2 : (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) +
    (c^3 + 3 * a^3) / (5 * c + a) - 2 / 3 * (a^2 + b^2 + c^2) ≥ 0 := by
    have h3 : (5 * a + b) > 0 := by positivity
    have h4 : (5 * b + c) > 0 := by positivity
    have h5 : (5 * c + a) > 0 := by positivity
    have h6 : (5 * a + b) * (5 * b + c) * (5 * c + a) > 0 := by positivity
    have h7 : (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) +
      (c^3 + 3 * a^3) / (5 * c + a) - 2 / 3 * (a^2 + b^2 + c^2) =
      ((a^3 + 3 * b^3) * (5 * b + c) * (5 * c + a) +
      (b^3 + 3 * c^3) * (5 * a + b) * (5 * c + a) +
      (c^3 + 3 * a^3) * (5 * a + b) * (5 * b + c) - 2 / 3 * (a^2 + b^2 + c^2) * (5 * a + b) * (5 * b + c) * (5 * c + a)) / ((5 * a + b) * (5 * b + c) * (5 * c + a)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
        sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a)]
    all_goals positivity
  linarith