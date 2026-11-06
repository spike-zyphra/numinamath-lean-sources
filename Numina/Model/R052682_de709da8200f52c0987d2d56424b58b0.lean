import Mathlib

theorem inequalities_599174 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : 0 < a + b := by nlinarith
  have h2 : 0 < a + c := by nlinarith
  have h3 : 0 < b + c := by nlinarith
  have h4 : 0 < (b + c) * (c + a) * (a + b) := by positivity
  have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    -- Using the squared terms as non-negative.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity
  linarith