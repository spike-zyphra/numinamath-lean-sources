import Mathlib

theorem inequalities_601812 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b + c) * (1 / a + 1 / b + 1 / c) = 10) :
    31 / 3 ≤ (b^2 + c^2) / a^2 + (b^2 + a^2) / c^2 + (a^2 + c^2) / b^2 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h7 : (b^2 + c^2) / a^2 + (b^2 + a^2) / c^2 + (a^2 + c^2) / b^2 - 31 / 3 ≥ 0 := by
    have h8 : 0 < a^2 * b^2 * c^2 := by positivity
    have h9 : (b^2 + c^2) / a^2 + (b^2 + a^2) / c^2 + (a^2 + c^2) / b^2 - 31 / 3 =
        ( (b^2 + c^2) * b^2 * c^2 + (b^2 + a^2) * a^2 * b^2 + (a^2 + c^2) * a^2 * c^2 - (31 / 3) * a^2 * b^2 * c^2 ) / (a^2 * b^2 * c^2) := by
      field_simp
      <;> ring
    rw [h9]
    have h10 : (b^2 + c^2) * b^2 * c^2 + (b^2 + a^2) * a^2 * b^2 + (a^2 + c^2) * a^2 * c^2 - (31 / 3) * a^2 * b^2 * c^2 ≥ 0 := by
      field_simp at h ⊢
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith