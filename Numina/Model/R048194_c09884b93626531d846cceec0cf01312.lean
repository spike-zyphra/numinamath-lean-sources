import Mathlib
theorem inequalities_280602 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 := by
  have h4 : 0 < 1 + a + b := by
    nlinarith
  have h5 : 0 < 1 + b + c := by
    nlinarith
  have h6 : 0 < 1 + c + a := by
    nlinarith
  have h7 : 0 < (1 + a + b) * (1 + b + c) * (1 + c + a) := by
    positivity
  have h8 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1 ≤ 0 := by
    have h9 : (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1) = ( (1 + b + c) * (1 + c + a) + (1 + a + b) * (1 + c + a) + (1 + a + b) * (1 + b + c) - (1 + a + b) * (1 + b + c) * (1 + c + a) ) / ( (1 + a + b) * (1 + b + c) * (1 + c + a) ) := by
      field_simp
      ring
    rw [h9] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
                  sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
              ]
    · -- Show denominator is ≥ 0
      positivity
  linarith