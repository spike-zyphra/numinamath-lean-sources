import Mathlib

theorem inequalities_76614 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : (a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h3 : 0 < a * b * c := h1
    have h4 : (a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / a + 1 / b + 1 / c) =
        ( (a^2 * c + b^2 * a + c^2 * b)^2 - a * b * c * (a + b + c) * (a * b + a * c + b * c) ) / (a^2 * b^2 * c^2) := by
      field_simp
      ring_nf
    rw [h4] at *
    apply div_nonneg
    have h5 : (a^2 * c + b^2 * a + c^2 * b) ^ 2 - a * b * c * (a + b + c) * (a * b + a * c + b * c) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a)
        ]
    linarith [h5]
    all_goals positivity
  linarith only [h2]