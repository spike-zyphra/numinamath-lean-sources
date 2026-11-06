import Mathlib

theorem algebra_166603 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + a * b + b^2 = 9) (h2 : b^2 + b * c + c^2 = 52) (h3 : c^2 + c * a + a^2 = 49) :
    (49 * b^2 - 33 * b * c + 9 * c^2) / a^2 = 52 := by
  have h4 : 49 * b^2 - 33 * b * c + 9 * c^2 = 52 * a^2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h6 : (49 * b^2 - 33 * b * c + 9 * c^2) / a^2 = 52 := by
    rw [h4]
    field_simp
    <;> nlinarith
  exact h6