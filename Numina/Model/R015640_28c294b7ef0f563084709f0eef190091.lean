import Mathlib

theorem inequalities_3677 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  a^2 / b + b^2 / a ≥ Real.sqrt (2 * (a^2 + b^2)) + 3 * (a - b)^2 / (a + b) := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a + b := by linarith
  have h3 : a^2 / b + b^2 / a - 3 * (a - b)^2 / (a + b) ≥ Real.sqrt (2 * (a^2 + b^2)) := by
    have h4 : a^2 / b + b^2 / a - 3 * (a - b)^2 / (a + b) = (a^3 + b^3) / (a * b) - 3 * (a - b)^2 / (a + b) := by
      field_simp
      <;> ring
    rw [h4]
    have h5 : (a^3 + b^3) / (a * b) - 3 * (a - b)^2 / (a + b) ≥ Real.sqrt (2 * (a^2 + b^2)) := by
      have h6 : (a^3 + b^3) / (a * b) - 3 * (a - b)^2 / (a + b) - Real.sqrt (2 * (a^2 + b^2)) ≥ 0 := by
        have h7 : 0 < a * b * (a + b) := by positivity
        have h8 : (a^3 + b^3) / (a * b) - 3 * (a - b)^2 / (a + b) - Real.sqrt (2 * (a^2 + b^2)) =
          ((a^3 + b^3) * (a + b) - 3 * (a - b)^2 * (a * b) - Real.sqrt (2 * (a^2 + b^2)) * (a * b * (a + b))) / (a * b * (a + b)) := by
          field_simp
          <;> ring
        rw [h8] at *
        apply div_nonneg
        -- Show that the numerator is non-negative.
        nlinarith [Real.sqrt_nonneg (2 * (a^2 + b^2)), sq_nonneg ((a^3 + b^3) * (a + b) - 3 * (a - b)^2 * (a * b) - Real.sqrt (2 * (a^2 + b^2)) * (a * b * (a + b))), 
                  sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a * (a - b) - b * (a - b)), 
                  sq_nonneg (a * b), 
                  sq_nonneg (a + b - Real.sqrt (2 * (a^2 + b^2))), 
                  Real.sq_sqrt (show 0 ≤ (2 * (a^2 + b^2) : ℝ) by positivity), 
                  mul_pos ha hb, 
                  mul_pos ha (show 0 < b ^ 2 by positivity), 
                  mul_pos (show 0 < a ^ 2 by positivity) hb, 
                  mul_pos (show 0 < a * b by positivity) (show 0 < (a + b) by positivity), 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)]
        all_goals positivity
      linarith [Real.sqrt_nonneg (2 * (a^2 + b^2))]
    linarith [Real.sqrt_nonneg (2 * (a^2 + b^2))]
  linarith [h3, Real.sqrt_nonneg (2 * (a^2 + b^2))]