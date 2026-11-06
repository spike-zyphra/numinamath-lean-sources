import Mathlib

theorem inequalities_126634 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    4 ≤ a / b + b / c + c / d + d / a := by
  have h1 : 0 < a * b * c * d := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    all_goals nlinarith

  have h2 : a / b + b / c + c / d + d / a - 4 ≥ 0 := by 
    have h3 : a / b + b / c + c / d + d / a - 4 = (a^2 * c * d + b^2 * a * d + c^2 * a * b + d^2 * b * c - 4 * (a * b * c * d)) / (a * b * c * d) := by
      field_simp
      ring
    rw [h3] 
    have h4 : a^2 * c * d + b^2 * a * d + c^2 * a * b + d^2 * b * c - 4 * (a * b * c * d) ≥ 0 := by
      nlinarith [sq_nonneg (a * c - b * a), sq_nonneg (b * d - c * b), sq_nonneg (c * a - d * c), sq_nonneg (d * b - a * d),
          sq_nonneg (a * d - b * c), sq_nonneg (b * a - c * d), sq_nonneg (c * b - d * a),
          sq_nonneg (a - b), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (c - d),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
    apply div_nonneg
    · exact h4
    · positivity
  linarith