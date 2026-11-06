import Mathlib

theorem inequalities_602257 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b^2 / a^2 + c^2 / b^2 + a^2 / c^2 + 3 ≥ 2 * (a / b + b / c + c / a) := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 0 < a^2 * b^2 * c^2 := by
    positivity
  have h3 : b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2 + 3 - 2 * (a / b + b / c + c / a) ≥ 0 := by
    have h4 : b ^ 2 / a ^ 2 + c ^ 2 / b ^ 2 + a ^ 2 / c ^ 2 + 3 - 2 * (a / b + b / c + c / a) =
        ( (b ^ 4 * c ^ 2 + a ^ 2 * c ^ 4 + a ^ 4 * b ^ 2 + 3 * a^2 * b^2 * c^2 - 2 * (a^3 * b * c ^ 2 + a^2 * b ^ 3 * c + a * b ^ 2 * c ^ 3)) ) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h4]
    have h5 : (b ^ 4 * c ^ 2 + a ^ 2 * c ^ 4 + a ^ 4 * b ^ 2 + 3 * a^2 * b^2 * c^2 - 2 * (a^3 * b * c ^ 2 + a^2 * b ^ 3 * c + a * b ^ 2 * c ^ 3)) ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b), 
                sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2), 
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
                sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
                mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
                sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b), sq_nonneg (c * b - a * c)
                ]
    have h6 : ( (b ^ 4 * c ^ 2 + a ^ 2 * c ^ 4 + a ^ 4 * b ^ 2 + 3 * a^2 * b^2 * c^2 - 2 * (a^3 * b * c ^ 2 + a^2 * b ^ 3 * c + a * b ^ 2 * c ^ 3)) ) / (a^2 * b^2 * c^2) ≥ 0 := by
      apply div_nonneg
      nlinarith
      positivity
    linarith
  linarith [h3]