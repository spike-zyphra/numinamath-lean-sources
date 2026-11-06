import Mathlib

theorem inequalities_600714 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b / (a ^ 2 + b ^ 2 + 2 * c ^ 2) + b * c / (2 * a ^ 2 + b ^ 2 + c ^ 2) +
    c * a / (a ^ 2 + 2 * b ^ 2 + c ^ 2) ≤ 3 / 4 := by 
  have h1 : 0 < a ^ 2 + b ^ 2 + 2 * c ^ 2 := by positivity
  have h2 : 0 < 2 * a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have h3 : 0 < a ^ 2 + 2 * b ^ 2 + c ^ 2 := by positivity
  have h4 : a * b / (a ^ 2 + b ^ 2 + 2 * c ^ 2) + b * c / (2 * a ^ 2 + b ^ 2 + c ^ 2) + c * a / (a ^ 2 + 2 * b ^ 2 + c ^ 2) - 3 / 4 ≤ 0 := by
    have h5 : a * b / (a ^ 2 + b ^ 2 + 2 * c ^ 2) + b * c / (2 * a ^ 2 + b ^ 2 + c ^ 2) + c * a / (a ^ 2 + 2 * b ^ 2 + c ^ 2) - 3 / 4 =
        ( (a * b * (2 * a^2 + b^2 + c^2) * (a^2 + 2 * b^2 + c^2) ) +
          (b * c * (a^2 + b^2 + 2 * c^2) * (a^2 + 2 * b^2 + c^2) ) +
          (c * a * (a^2 + b^2 + 2 * c^2) * (2 * a^2 + b^2 + c^2) ) - 3 / 4 * (a^2 + b^2 + 2 * c^2) * (2 * a^2 + b^2 + c^2) * (a^2 + 2 * b^2 + c^2) ) / ( (a^2 + b^2 + 2 * c^2) * (2 * a^2 + b^2 + c^2) * (a^2 + 2 * b^2 + c^2) ) := by
      field_simp
      ring
    rw [h5] 
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
                sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- Prove denominator is ≥ 0
      positivity
  linarith