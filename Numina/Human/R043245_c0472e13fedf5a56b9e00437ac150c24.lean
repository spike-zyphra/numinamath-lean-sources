import Mathlib

theorem inequalities_200116 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ a / b + b / c + c / a := by
  have h1 : a / b + b / c + c / a - 3 ≥ 0 := by
    have h2 : a / b + b / c + c / a - 3 = (a^2 * c + b^2 * a + c^2 * b - 3 * a * b * c) / (a * b * c) := by
      field_simp
      ring
    rw [h2]
    have h3 : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h4 : a^2 * c + b^2 * a + c^2 * b - 3 * a * b * c ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h5 : (a^2 * c + b^2 * a + c^2 * b - 3 * a * b * c) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  linarith [h1]