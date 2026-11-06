import Mathlib

theorem inequalities_5491 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a / c + c / a ≤ ((a * d + b * c) * (a * b + c * d)) / (a * b * c * d) - 2 := by
  have h1 : 0 < a * b * c * d := by
    positivity
  have h2 : a / c + c / a - (( (a * d + b * c) * (a * b + c * d) ) / (a * b * c * d) - 2 ) ≤ 0 := by
    have pos1 : 0 < a * b * c * d := h1
    have eq : a / c + c / a - (( (a * d + b * c) * (a * b + c * d) ) / (a * b * c * d) - 2 ) =
        ( (a^2 * b * d + c^2 * b * d ) - ( (a * d + b * c) * (a * b + c * d ) - 2 * (a * b * c * d) ) ) / (a * b * c * d) := by
      field_simp
      ring
    rw [eq] at *
    apply div_nonpos_of_nonpos_of_nonneg
    -- Prove numerator is nonpositive
    nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), sq_nonneg (a * c - b * d), sq_nonneg (a * d - c * b), sq_nonneg (a * (d - b) - c * (d - b)), sq_nonneg (a * c - b * d), sq_nonneg (a - c), sq_nonneg (b - d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd 
      ]
    -- Prove denominator is nonnegative
    positivity
  linarith