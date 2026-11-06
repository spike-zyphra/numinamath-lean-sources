import Mathlib

theorem inequalities_3657
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    3 * (a / b + b / c + c / a) +
    8 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ≥ 17 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : 0 < a * b * c := mul_pos h1 hc
  have h5 : 0 < a * b + b * c + c * a := by linarith [h1, h2, h3]
  have h6 : 3 * (a / b + b / c + c / a) +
    8 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) - 17 ≥ 0 := by
    have pos1 : 0 < a * b * c * (a * b + b * c + c * a) := by positivity
    have eq1 : 3 * (a / b + b / c + c / a) +
        8 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) - 17 =
        (3 * (a^2 * c + b^2 * a + c^2 * b) * (a * b + b * c + c * a) +
          8 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b * c) - 17 * (a * b * c) * (a * b + b * c + c * a)) / (a * b * c * (a * b + b * c + c * a)) := by
      field_simp
      ring
    rw [eq1] at *
    apply div_nonneg
    -- Prove numerator is non-negative
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
          sq_nonneg (a * (a - c) + b * (b - a) + c * (c - b)), 
          sq_nonneg (a * (b - c) + b * (c - a) + c * (a - b)), 
          sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b), 
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
          mul_pos (show 0 < a * b from by nlinarith [ha, hb]) (show 0 < b * c from by nlinarith [hb, hc]), 
          mul_pos (show 0 < a * b from by nlinarith [ha, hb]) (show 0 < c * a from by nlinarith [hc, ha]), 
          mul_pos (show 0 < b * c from by nlinarith [hb, hc]) (show 0 < c * a from by nlinarith [hc, ha])]
    all_goals positivity
  linarith