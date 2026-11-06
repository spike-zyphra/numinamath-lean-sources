import Mathlib

theorem inequalities_352 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3/4 ≤ (a^2 - b * c + c^2)/(2 * a^2 + b^2 + c^2) +
    (b^2 - c * a + a^2)/(a^2 + 2 * b^2 + c^2) +
    (c^2 - a * b + b^2)/(a^2 + b^2 + 2 * c^2) := by 
  have pos1 : 0 < 2 * a^2 + b^2 + c^2 := by positivity
  have pos2 : 0 < a^2 + 2 * b^2 + c^2 := by positivity
  have pos3 : 0 < a^2 + b^2 + 2 * c^2 := by positivity
  have h1 : (a^2 - b * c + c^2)/(2 * a^2 + b^2 + c^2) +
      (b^2 - c * a + a^2)/(a^2 + 2 * b^2 + c^2) +
      (c^2 - a * b + b^2)/(a^2 + b^2 + 2 * c^2) - 3/4 ≥ 0 := by 
    have h2 : (a^2 - b * c + c^2)/(2 * a^2 + b^2 + c^2) +
        (b^2 - c * a + a^2)/(a^2 + 2 * b^2 + c^2) +
        (c^2 - a * b + b^2)/(a^2 + b^2 + 2 * c^2) - 3/4 =
        ( (a^2 - b * c + c^2) * (a^2 + 2 * b^2 + c^2) * (a^2 + b^2 + 2 * c^2) +
        (b^2 - c * a + a^2) * (2 * a^2 + b^2 + c^2) * (a^2 + b^2 + 2 * c^2) +
        (c^2 - a * b + b^2) * (2 * a^2 + b^2 + c^2) * (a^2 + 2 * b^2 + c^2) - 3 / 4 * (2 * a^2 + b^2 + c^2) * (a^2 + 2 * b^2 + c^2) * (a^2 + b^2 + 2 * c^2) ) / ( (2 * a^2 + b^2 + c^2) * (a^2 + 2 * b^2 + c^2) * (a^2 + b^2 + 2 * c^2) ) := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
      sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc),
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * a from mul_pos hc ha),
      mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < c * a from mul_pos hc ha)
    ]
    all_goals positivity
  linarith