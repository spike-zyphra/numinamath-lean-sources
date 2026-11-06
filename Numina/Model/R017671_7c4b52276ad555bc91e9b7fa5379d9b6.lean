import Mathlib

theorem inequalities_603094 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c - a) / (5 * a^2 + 4 * b * c) + (c + a - b) / (5 * b^2 + 4 * c * a) +
    (a + b - c) / (5 * c^2 + 4 * a * b) ≥ 1 / (a + b + c) := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith 
  have ha1 : 0 < 5 * a^2 + 4 * b * c := by positivity
  have hb1 : 0 < 5 * b^2 + 4 * c * a := by positivity
  have hc1 : 0 < 5 * c^2 + 4 * a * b := by positivity
  have ha2 : 0 < a + b + c := by positivity

  have h2 : (b + c - a) / (5 * a^2 + 4 * b * c) + (c + a - b) / (5 * b^2 + 4 * c * a) + (a + b - c) / (5 * c^2 + 4 * a * b) - 1 / (a + b + c) ≥ 0 := by 
    have h3 : (b + c - a) / (5 * a^2 + 4 * b * c) + (c + a - b) / (5 * b^2 + 4 * c * a) + (a + b - c) / (5 * c^2 + 4 * a * b) - 1 / (a + b + c) =
        ((b + c - a) * (5 * b^2 + 4 * c * a) * (5 * c^2 + 4 * a * b) * (a + b + c) + (c + a - b) * (5 * a^2 + 4 * b * c) * (5 * c^2 + 4 * a * b) * (a + b + c) + (a + b - c) * (5 * a^2 + 4 * b * c) * (5 * b^2 + 4 * c * a) * (a + b + c) - (5 * a^2 + 4 * b * c) * (5 * b^2 + 4 * c * a) * (5 * c^2 + 4 * a * b)) / ((5 * a^2 + 4 * b * c) * (5 * b^2 + 4 * c * a) * (5 * c^2 + 4 * a * b) * (a + b + c)) := by 
      field_simp
      <;> ring 
    rw [h3] at *
    have h3 : (b + c - a) * (5 * b^2 + 4 * c * a) * (5 * c^2 + 4 * a * b) * (a + b + c) + (c + a - b) * (5 * a^2 + 4 * b * c) * (5 * c^2 + 4 * a * b) * (a + b + c) + (a + b - c) * (5 * a^2 + 4 * b * c) * (5 * b^2 + 4 * c * a) * (a + b + c) - (5 * a^2 + 4 * b * c) * (5 * b^2 + 4 * c * a) * (5 * c^2 + 4 * a * b) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        mul_pos (mul_pos ha hb) hc,
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
        mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc),
        mul_nonneg (mul_nonneg (le_of_lt hb) (le_of_lt hc)) (le_of_lt ha)
      ]
    apply div_nonneg 
    · linarith 
    all_goals positivity

  linarith