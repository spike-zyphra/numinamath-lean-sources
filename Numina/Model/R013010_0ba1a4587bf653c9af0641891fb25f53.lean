import Mathlib

theorem inequalities_997 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    27 + (2 + a^2 / (b * c)) * (2 + b^2 / (a * c)) * (2 + c^2 / (a * b)) ≥
    6 * (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  have pos1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h1 : 27 + (2 + a^2 / (b * c)) * (2 + b^2 / (a * c)) * (2 + c^2 / (a * b)) - 6 * (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h1' : 27 + (2 + a^2 / (b * c)) * (2 + b^2 / (a * c)) * (2 + c^2 / (a * b)) - 6 * (a + b + c) * (1 / a + 1 / b + 1 / c) =
        (27 * a^2 * b^2 * c^2 + (2 * b * c + a^2) * (2 * a * c + b^2) * (2 * a * b + c^2) - 6 * (a + b + c) * (a * b + b * c + c * a) * (a * b * c)) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h1'] at *
    have h2 : 27 * a^2 * b^2 * c^2 + (2 * b * c + a^2) * (2 * a * c + b^2) * (2 * a * b + c^2) ≥ 6 * (a + b + c) * (a * b + b * c + c * a) * (a * b * c) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a * b - b * c)), sq_nonneg (b * (a * b - b * c)), sq_nonneg (c * (a * b - b * c)),
          sq_nonneg (a * (b * c - c * a)), sq_nonneg (b * (b * c - c * a)), sq_nonneg (c * (b * c - c * a)),
          sq_nonneg (a * (c * a - a * b)), sq_nonneg (b * (c * a - a * b)), sq_nonneg (c * (c * a - a * b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (mul_pos ha hb) hc]
    have h3 : 27 * a^2 * b^2 * c^2 + (2 * b * c + a^2) * (2 * a * c + b^2) * (2 * a * b + c^2) - 6 * (a + b + c) * (a * b + b * c + c * a) * (a * b * c) ≥ 0 := by
      nlinarith [h2]
    have h4 : (27 * a^2 * b^2 * c^2 + (2 * b * c + a^2) * (2 * a * c + b^2) * (2 * a * b + c^2) - 6 * (a + b + c) * (a * b + b * c + c * a) * (a * b * c)) / (a^2 * b^2 * c^2) ≥ 0 := by
      have pos1' : a^2 * b^2 * c^2 > 0 := by
        positivity
      apply div_nonneg
      · linarith [h3]
      all_goals positivity
    linarith [h4]
  linarith [h1]