import Mathlib

theorem inequalities_254430 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
1 / a + 1 / b + 1 / c ≤ (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) := by
  have pos1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h1 : 1 / a + 1 / b + 1 / c - (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) ≤ 0 := by
    have h2 : (1 / a + 1 / b + 1 / c) - (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) =
        (( (b * c + a * c + a * b ) * a^2 * b^2 * c^2 ) - ( a^8 + b^8 + c^8 )) / (a^3 * b^3 * c^3) := by 
      field_simp
      ring
    rw [h2] at *
    apply div_nonpos_of_nonpos_of_nonneg 
    -- Prove the numerator is ≤ 0
    nlinarith [sq_nonneg (a^4 - b^4), sq_nonneg (b^4 - c^4), sq_nonneg (c^4 - a^4),
      sq_nonneg (a^3 - b^3), sq_nonneg (b^3 - c^3), sq_nonneg (c^3 - a^3),
      sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a^2 from by positivity) (show 0 < b^2 from by positivity), 
      mul_pos (show 0 < a^2 from by positivity) (show 0 < c^2 from by positivity), 
      mul_pos (show 0 < b^2 from by positivity) (show 0 < c^2 from by positivity),
      sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
      mul_pos (mul_pos ha hb) hc
    ]
    -- Prove the denominator is ≥ 0
    positivity 
  linarith [h1]