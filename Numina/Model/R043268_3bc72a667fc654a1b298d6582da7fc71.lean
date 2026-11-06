import Mathlib

theorem inequalities_601913 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c ≥ 1) :
    (a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) +
    (c + 1) / (c ^ 2 + c + 1) ≤ 2 := by 
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : a ^ 2 + a + 1 > 0 := by
    nlinarith [sq_nonneg (a + 1 / 2)]
  have h3 : b ^ 2 + b + 1 > 0 := by
    nlinarith [sq_nonneg (b + 1 / 2)]
  have h4 : c ^ 2 + c + 1 > 0 := by
    nlinarith [sq_nonneg (c + 1 / 2)]
  have h6 : (a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) + (c + 1) / (c ^ 2 + c + 1) - 2 ≤ 0 := by
    have h7 : (a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) + (c + 1) / (c ^ 2 + c + 1) - 2 =
          ((a + 1) * (b^2 + b + 1) * (c^2 + c + 1) +
          (b + 1) * (a^2 + a + 1) * (c^2 + c + 1) +
          (c + 1) * (a^2 + a + 1) * (b^2 + b + 1) - 2 * (a^2 + a + 1) * (b^2 + b + 1) * (c^2 + c + 1)) / ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) := by
      field_simp
      ring
    rw [h7]
    have h8 : ((a + 1) * (b^2 + b + 1) * (c^2 + c + 1) + (b + 1) * (a^2 + a + 1) * (c^2 + c + 1) + (c + 1) * (a^2 + a + 1) * (b^2 + b + 1) - 2 * (a^2 + a + 1) * (b^2 + b + 1) * (c^2 + c + 1)) / ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) ≤ 0 := by
      have h9 : 0 < (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by
        positivity
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1)]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith
  linarith