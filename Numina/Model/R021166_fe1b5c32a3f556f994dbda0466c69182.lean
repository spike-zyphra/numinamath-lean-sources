import Mathlib

open Real

theorem inequalities_1706 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 5 ≤ (a + b - c)^2 / (a^2 + b^2 + c^2 + 2 * a * b) +
           (b + c - a)^2 / (b^2 + c^2 + a^2 + 2 * b * c) +
           (c + a - b)^2 / (c^2 + a^2 + b^2 + 2 * c * a) := by
  have pos1 : 0 < a^2 + b^2 + c^2 + 2 * a * b := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have pos2 : 0 < b^2 + c^2 + a^2 + 2 * b * c := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have pos3 : 0 < c^2 + a^2 + b^2 + 2 * c * a := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h4 : (a + b - c)^2 / (a^2 + b^2 + c^2 + 2 * a * b) + (b + c - a)^2 / (b^2 + c^2 + a^2 + 2 * b * c) + (c + a - b)^2 / (c^2 + a^2 + b^2 + 2 * c * a) - 3 / 5 ≥ 0 := by
    have h4 : 0 < (a^2 + b^2 + c^2 + 2 * a * b) * (b^2 + c^2 + a^2 + 2 * b * c) * (c^2 + a^2 + b^2 + 2 * c * a) := by positivity
    have h5 : (a + b - c)^2 / (a^2 + b^2 + c^2 + 2 * a * b) + (b + c - a)^2 / (b^2 + c^2 + a^2 + 2 * b * c) + (c + a - b)^2 / (c^2 + a^2 + b^2 + 2 * c * a) - 3 / 5 =
          ( (a + b - c)^2 * (b^2 + c^2 + a^2 + 2 * b * c) * (c^2 + a^2 + b^2 + 2 * c * a) +
            (b + c - a)^2 * (a^2 + b^2 + c^2 + 2 * a * b) * (c^2 + a^2 + b^2 + 2 * c * a) +
            (c + a - b)^2 * (a^2 + b^2 + c^2 + 2 * a * b) * (b^2 + c^2 + a^2 + 2 * b * c) - 3 / 5 * (a^2 + b^2 + c^2 + 2 * a * b) * (b^2 + c^2 + a^2 + 2 * b * c) * (c^2 + a^2 + b^2 + 2 * c * a) ) / ( (a^2 + b^2 + c^2 + 2 * a * b) * (b^2 + c^2 + a^2 + 2 * b * c) * (c^2 + a^2 + b^2 + 2 * c * a) ) := by
      field_simp
      <;> ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    all_goals
      positivity
  linarith