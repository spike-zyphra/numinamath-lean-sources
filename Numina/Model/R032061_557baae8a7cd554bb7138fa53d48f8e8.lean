import Mathlib

theorem inequalities_315881 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c ≤ (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : a * b * c > 0 := h1
  have h3 : 0 < a^3 * b^3 * c^3 := by positivity
  have h4 : 1 / a + 1 / b + 1 / c - (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) ≤ 0 := by
    have pos1 : 0 < a^3 * b^3 * c^3 := by positivity
    have h5 : 1 / a + 1 / b + 1 / c - (a^8 + b^8 + c^8) / (a^3 * b^3 * c^3) =
        ( (a^2 * b^3 * c^3 + a^3 * b^2 * c^3 + a^3 * b^3 * c^2 ) - (a^8 + b^8 + c^8) ) / (a^3 * b^3 * c^3) := by
      field_simp
      ring_nf
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      nlinarith [sq_nonneg (a^4 - b^4), sq_nonneg (a^4 - c^4), sq_nonneg (b^4 - c^4),
          sq_nonneg (a^3 - b^3), sq_nonneg (a^3 - c^3), sq_nonneg (b^3 - c^3),
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c)]
    · -- Show that the denominator is non-negative
      positivity
  linarith