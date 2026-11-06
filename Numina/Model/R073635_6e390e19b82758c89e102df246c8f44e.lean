import Mathlib

theorem inequalities_599281 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / a ≥ a + b + c := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / a - (a + b + c) ≥ 0 := by
    have h3 : a ^ 2 / b + b ^ 2 / c + c ^ 2 / a - (a + b + c) = 
      (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b - (a * b * c) * (a + b + c)) / (a * b * c) := by
      field_simp
      ring
    rw [h3]
    have h4 : a ^ 3 * c + b ^ 3 * a + c ^ 3 * b - (a * b * c) * (a + b + c) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h5 : a * b * c > 0 := h1
    apply div_nonneg
    linarith
    positivity
  linarith