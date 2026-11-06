import Mathlib

theorem inequalities_318107 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b) ≥ a + b + c := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b) - (a + b + c) ≥ 0 := by
    have h3 : a^3 / (b * c) + b^3 / (a * c) + c^3 / (a * b) - (a + b + c) =
      (a^4 + b^4 + c^4 - (a^2 * b * c + a * b^2 * c + a * b * c^2)) / (a * b * c) := by
      field_simp [show 0 < b * c by positivity, show 0 < a * c by positivity, show 0 < a * b by positivity]
      ring_nf
      <;> field_simp [show 0 < b * c by positivity, show 0 < a * c by positivity, show 0 < a * b by positivity]
      <;> ring_nf
    rw [h3]
    have h4 : a^4 + b^4 + c^4 - (a^2 * b * c + a * b^2 * c + a * b * c^2) ≥ 0 := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a * a - b * b), sq_nonneg (b * b - c * c), sq_nonneg (c * c - a * a),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonneg
    · linarith
    · positivity
  linarith