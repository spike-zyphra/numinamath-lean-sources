import Mathlib

theorem inequalities_8885
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a / b + b / c + c / a) * (a / (a + b) + b / (b + c) + c / (c + a)) ≥ 9 / 2 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h4 : (a / b + b / c + c / a) * (a / (a + b) + b / (b + c) + c / (c + a)) - 9 / 2 ≥ 0 := by
    have pos1 : 0 < a * b * c := h1
    have pos2 : 0 < (a + b) * (b + c) * (c + a) := by
      positivity
    have pos3 : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by
      positivity
    have h5 : (a / b + b / c + c / a) * (a / (a + b) + b / (b + c) + c / (c + a)) - 9 / 2 = ( (a^2 * c + b^2 * a + c^2 * b) * (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c)) - (9 / 2) * a * b * c * (a + b) * (b + c) * (c + a) ) / ( a * b * c * (a + b) * (b + c) * (c + a) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    . -- Show that the numerator is non-negative.
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc ]
    . -- Show that the denominator is positive.
      positivity
  linarith