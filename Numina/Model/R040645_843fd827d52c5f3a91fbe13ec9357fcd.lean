import Mathlib

theorem inequalities_598105 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) ≤ 1 := by
  have h1 : 0 < a * b * c := by positivity
  have h2 : a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) - 1 ≤ 0 := by
    have pos1 : 0 < a * b + a + 1 := by positivity
    have pos2 : 0 < b * c + b + 1 := by positivity
    have pos3 : 0 < c * a + c + 1 := by positivity
    have h3 : a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) - 1 =
        ( a * (b * c + b + 1) * (c * a + c + 1) + 
          b * (a * b + a + 1) * (c * a + c + 1) + 
          c * (a * b + a + 1) * (b * c + b + 1) - 
          (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1) ) / ( (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1) ) := by
      field_simp
      <;> ring
      <;> field_simp
    rw [h3] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator is ≤ 0
      nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                mul_pos (mul_pos ha hb) hc
              ]
    · -- Show denominator is ≥ 0
      positivity
  linarith