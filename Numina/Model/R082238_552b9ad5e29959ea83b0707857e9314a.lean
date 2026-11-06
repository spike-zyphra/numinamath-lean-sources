import Mathlib

theorem inequalities_133672 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) > 1 / 2 := by
  have h1 : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) - 1 / 2 > 0 := by
    have h2 : 0 < b + 2 * c := by nlinarith
    have h3 : 0 < c + 2 * a := by nlinarith
    have h4 : 0 < a + 2 * b := by nlinarith
    have h5 : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) - 1 / 2 =
      (a * (c + 2 * a) * (a + 2 * b) + b * (b + 2 * c) * (a + 2 * b) + c * (b + 2 * c) * (c + 2 * a) - 1 / 2 * (b + 2 * c) * (c + 2 * a) * (a + 2 * b)) / ((b + 2 * c) * (c + 2 * a) * (a + 2 * b)) := by
      field_simp
      ring
    rw [h5] at *
    have h6 : 0 < (b + 2 * c) * (c + 2 * a) * (a + 2 * b) := by
      positivity
    have h7 : a * (c + 2 * a) * (a + 2 * b) + b * (b + 2 * c) * (a + 2 * b) + c * (b + 2 * c) * (c + 2 * a) - 1 / 2 * (b + 2 * c) * (c + 2 * a) * (a + 2 * b) > 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_pos h7 (by positivity)
  linarith