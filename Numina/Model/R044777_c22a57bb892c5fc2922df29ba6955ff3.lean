import Mathlib

theorem inequalities_85805 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a + b + c + d) / (a * b * c * d) ≤ 1 / a ^ 3 + 1 / b ^ 3 + 1 / c ^ 3 + 1 / d ^ 3 := by
  have h1 : 0 < a * b * c * d := by positivity
  have h2 : (a + b + c + d) / (a * b * c * d) - (1 / a ^ 3 + 1 / b ^ 3 + 1 / c ^ 3 + 1 / d ^ 3) ≤ 0 := by
    have h4 : (a + b + c + d) / (a * b * c * d) - (1 / a ^ 3 + 1 / b ^ 3 + 1 / c ^ 3 + 1 / d ^ 3) =
        ((a + b + c + d) * (a^2 * b^2 * c^2 * d^2) - (b^3 * c^3 * d^3 + a^3 * c^3 * d^3 + a^3 * b^3 * d^3 + a^3 * b^3 * c^3)) / (a^3 * b^3 * c^3 * d^3) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - a * d), sq_nonneg (a * b - b * c), 
          sq_nonneg (a * b - b * d), sq_nonneg (a * b - c * d), sq_nonneg (a * c - a * d), 
          sq_nonneg (a * c - b * c), sq_nonneg (a * c - b * d), sq_nonneg (a * c - c * d), 
          sq_nonneg (a * d - b * c), sq_nonneg (a * d - b * d), sq_nonneg (a * d - c * d),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a * b * c - a * b * d), sq_nonneg (a * b * c - a * c * d), 
          sq_nonneg (a * b * c - b * c * d), sq_nonneg (a * b * d - a * c * d), 
          sq_nonneg (a * b * d - b * c * d), sq_nonneg (a * c * d - b * c * d),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd,
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
          mul_pos (mul_pos ha hb) (mul_pos ha hc), 
          mul_pos (mul_pos ha hb) (mul_pos ha hd), 
          mul_pos (mul_pos ha hb) (mul_pos hc hd), 
          mul_pos (mul_pos ha hc) (mul_pos ha hd), 
          mul_pos (mul_pos ha hc) (mul_pos hb hd), 
          mul_pos (mul_pos ha hd) (mul_pos hb hc)
      ]
    · -- Show that the denominator is non-negative
      positivity
  linarith