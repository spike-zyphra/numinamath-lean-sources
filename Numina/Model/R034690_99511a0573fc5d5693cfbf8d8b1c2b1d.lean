import Mathlib

theorem inequalities_600981 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b^2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 ≥
    2 * (a / b + b / c + c / a) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : b^2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 - 2 * (a / b + b / c + c / a) ≥ 0 := by
    have ha2 : 0 < a ^ 2 := by positivity
    have hb2 : 0 < b ^ 2 := by positivity
    have hc2 : 0 < c ^ 2 := by positivity
    have h3 : b ^ 2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 - 2 * (a / b + b / c + c / a) =
        (b ^ 4 * c ^ 2 + a ^ 2 * c ^ 4 + a ^ 4 * b ^ 2 + 3 * a^2 * b^2 * c^2 - 2 * (a^3 * b * c^2 + a^2 * b^3 * c + a * b^2 * c^3)) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (b ^ 2 * c - a * b ^ 2), sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (c ^ 2 * a - a ^ 2 * b), sq_nonneg (b ^ 2 * c - a * c ^ 2), sq_nonneg (a * b ^ 2 - c ^ 2 * a), sq_nonneg (b * c ^ 2 - a * b ^ 2), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < b * c by nlinarith) (show 0 < a * b by nlinarith)]
    all_goals positivity
  linarith