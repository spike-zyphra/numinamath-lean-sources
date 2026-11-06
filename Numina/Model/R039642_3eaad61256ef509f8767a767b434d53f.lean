import Mathlib

theorem inequalities_172268 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≤ a^2 / b^2 + b^2 / c^2 + c^2 / a^2 := by
  have h1 : 0 < a * b * c := by positivity
  have h2 : a / b + b / c + c / a - (a^2 / b^2 + b^2 / c^2 + c^2 / a^2) ≤ 0 := by
    have eq2 : a / b + b / c + c / a - (a^2 / b^2 + b^2 / c^2 + c^2 / a^2) = 
        (a^3 * b * c^2 + a^2 * b^3 * c + a * b^2 * c^3 - (a^4 * c^2 + a^2 * b^4 + b^2 * c^4 )) / (a^2 * b^2 * c^2 ) := by
      field_simp
      ring
    rw [eq2] at *
    have h4 : a^3 * b * c^2 + a^2 * b^3 * c + a * b^2 * c^3 - (a^4 * c^2 + a^2 * b^4 + b^2 * c^4 ) ≤ 0 := by
      nlinarith [sq_nonneg (a^2 * c - a * b * c), sq_nonneg (b^2 * a - b * c * a), sq_nonneg (c^2 * b - c * a * b), 
        sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), 
        sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (b - a)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (mul_pos ha hb) (mul_pos hb hc), 
        mul_pos (mul_pos hb hc) (mul_pos ha hc), 
        mul_pos (mul_pos ha hb) (mul_pos hb hc)
      ]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [ h4 ]
    · -- Show the denominator is non-negative
      positivity 
  linarith