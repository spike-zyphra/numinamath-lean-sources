import Mathlib

theorem inequalities_597143 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≤ 1 := by
  have h3 : 0 < (a + b + 1) * (b + c + 1) * (c + a + 1) := by positivity
  have h4 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 ≤ 0 := by
    have h5 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 =
        ( (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1) ) / ( (a + b + 1) * (b + c + 1) * (c + a + 1) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove that the numerator is non-positive
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc ]
    · -- Prove that the denominator is non-negative
      positivity
  linarith