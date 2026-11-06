import Mathlib

theorem inequalities_603727 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b^2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 ≥ (a / b + b / c + c / a) := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have pos1 : 0 < a ^ 2 * b ^ 2 * c ^ 2 := mul_pos (mul_pos ha2 hb2) (hc2)
  have h : b^2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 - (a / b + b / c + c / a) ≥ 0 := by
    have h1 : b^2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 - (a / b + b / c + c / a) = (b^4 * c^2 + c^4 * a^2 + a^4 * b^2 + 3 * a^2 * b^2 * c^2 - (a^3 * b * c^2 + b^3 * a^2 * c + c^3 * b^2 * a)) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h1]
    apply div_nonneg
    nlinarith [sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b),
              sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a * b * c - b * c * a), sq_nonneg (a * b * c - c * a * b), 
              sq_nonneg (a^2 * b^2 - b^2 * c^2), sq_nonneg (b^2 * c^2 - c^2 * a^2), sq_nonneg (c^2 * a^2 - a^2 * b^2), 
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
              mul_pos ha2 hb2, mul_pos hb2 hc2, mul_pos ha2 hc2, 
              mul_pos (mul_pos ha hb) (mul_pos hb hc), 
              mul_pos (mul_pos hb hc) (mul_pos ha hc)]
    positivity
  linarith