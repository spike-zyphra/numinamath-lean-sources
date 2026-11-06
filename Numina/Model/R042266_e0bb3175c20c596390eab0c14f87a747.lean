import Mathlib

theorem inequalities_602082 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c ≤ (a ^ 8 + b ^ 8 + c ^ 8) / (a ^ 3 * b ^ 3 * c ^ 3) := by
  have h1 : 0 < a ^ 3 * b ^ 3 * c ^ 3 := by
    positivity
  have h2 : 1 / a + 1 / b + 1 / c - (a ^ 8 + b ^ 8 + c ^ 8) / (a ^ 3 * b ^ 3 * c ^ 3) ≤ 0 := by
    have h3 : 1 / a + 1 / b + 1 / c - (a ^ 8 + b ^ 8 + c ^ 8) / (a ^ 3 * b ^ 3 * c ^ 3) =
        (a^2 * b^3 * c^3 + a^3 * b^2 * c^3 + a^3 * b^3 * c^2 - (a ^ 8 + b ^ 8 + c ^ 8)) / (a^3 * b^3 * c^3) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonpos_of_nonpos_of_nonneg
    -- Prove that the numerator is less than 0
    nlinarith [sq_nonneg (a^4 - b^4), sq_nonneg (a^4 - c^4), sq_nonneg (b^4 - c^4),
          sq_nonneg (a^3 - b^3), sq_nonneg (a^3 - c^3), sq_nonneg (b^3 - c^3),
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos (show 0 < a by linarith) (show 0 < b by linarith),
          mul_pos (show 0 < a by linarith) (show 0 < c by linarith),
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith)
         ]
    -- Prove that the denominator is greater than 0
    positivity
  linarith