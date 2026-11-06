import Mathlib

theorem inequalities_60641
  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  (a + b) / c^2 + (c + a) / b^2 + (b + c) / a^2 ≥ 9 / (a + b + c) + 1 / a + 1 / b + 1 / c := by
  have pos1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have pos2 : 0 < a * b * c * (a + b + c) := mul_pos pos1 (show 0 < a + b + c by linarith)
  have pos3 : 0 < a^2 * b^2 * c^2 * (a + b + c) := by positivity

  have h1 : (a + b) / c^2 + (c + a) / b^2 + (b + c) / a^2 - (9 / (a + b + c) + 1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h2 : (a + b) / c^2 + (c + a) / b^2 + (b + c) / a^2 - (9 / (a + b + c) + 1 / a + 1 / b + 1 / c) =
        ( (a + b) * a^2 * b^2 * (a + b + c) + (c + a) * a^2 * c^2 * (a + b + c) + (b + c) * b^2 * c^2 * (a + b + c) - 9 * a^2 * b^2 * c^2 - a * b^2 * c^2 * (a + b + c) - b * a^2 * c^2 * (a + b + c) - c * a^2 * b^2 * (a + b + c) ) / (a^2 * b^2 * c^2 * (a + b + c)) := by
      field_simp
      ring
    rw [h2]
    have h3 : ( (a + b) * a^2 * b^2 * (a + b + c) + (c + a) * a^2 * c^2 * (a + b + c) + (b + c) * b^2 * c^2 * (a + b + c) - 9 * a^2 * b^2 * c^2 - a * b^2 * c^2 * (a + b + c) - b * a^2 * c^2 * (a + b + c) - c * a^2 * b^2 * (a + b + c) ) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonneg
    linarith
    all_goals positivity

  linarith