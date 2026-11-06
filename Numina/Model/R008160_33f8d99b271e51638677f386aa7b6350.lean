import Mathlib

theorem inequalities_620629 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) +
  c * a / (c + 3 * a + 2 * b) ≤ (a + b + c) / 6 := by 
  have h1 : 0 < a + 3 * b + 2 * c := by positivity
  have h2 : 0 < b + 3 * c + 2 * a := by positivity
  have h3 : 0 < c + 3 * a + 2 * b := by positivity
  have h4 : a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) + c * a / (c + 3 * a + 2 * b) - (a + b + c) / 6 ≤ 0 := by
    have h5 : a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) + c * a / (c + 3 * a + 2 * b) - (a + b + c) / 6 =
        (6 * a * b * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b) + 6 * b * c * (c + 3 * a + 2 * b) * (a + 3 * b + 2 * c) + 6 * c * a * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) - (a + b + c) * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b)) / (6 * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b)) := by
      field_simp
      ring
    rw [h5]
    have h6 : 6 * (a + 3 * b + 2 * c) * (b + 3 * c + 2 * a) * (c + 3 * a + 2 * b) > 0 := by positivity
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- Show denominator ≥ 0
      positivity
  linarith