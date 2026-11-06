import Mathlib

theorem inequalities_603439 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 + 8 * a ^ 2 * b ^ 2 * c ^ 2 / ((a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) ≤
    a * (b + c) / (b ^ 2 + c ^ 2) + b * (c + a) / (c ^ 2 + a ^ 2) +
    c * (a + b) / (a ^ 2 + b ^ 2) := by
  have h1 : 0 < a ^ 2 + b ^ 2 := by
    nlinarith
  have h2 : 0 < b ^ 2 + c ^ 2 := by
    nlinarith
  have h3 : 0 < c ^ 2 + a ^ 2 := by
    nlinarith
  have h4 : (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) > 0 := by
    positivity
  have h5 : a * (b + c) / (b ^ 2 + c ^ 2) + b * (c + a) / (c ^ 2 + a ^ 2) + c * (a + b) / (a ^ 2 + b ^ 2) - 2 - 8 * a ^ 2 * b ^ 2 * c ^ 2 / ((a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) ≥ 0 := by
    have h6 : a * (b + c) / (b ^ 2 + c ^ 2) + b * (c + a) / (c ^ 2 + a ^ 2) + c * (a + b) / (a ^ 2 + b ^ 2) - 2 - 8 * a ^ 2 * b ^ 2 * c ^ 2 / ((a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) =
        ( (a * (b + c) * (c ^ 2 + a ^ 2) * (a ^ 2 + b ^ 2) ) + (b * (c + a) * (b ^ 2 + c ^ 2) * (a ^ 2 + b ^ 2) ) + (c * (a + b) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ) - 2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) - 8 * a ^ 2 * b ^ 2 * c ^ 2 ) / ( (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) * (a ^ 2 + b ^ 2) ) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    · -- Prove the numerator is non-negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b) + a * (a - c) + b * (b - c) + b * (b - a) + c * (c - a) + c * (c - b)), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc ]
    · -- Prove the denominator is positive
      positivity
  linarith