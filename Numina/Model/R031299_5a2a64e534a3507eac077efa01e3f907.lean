import Mathlib

theorem inequalities_90363 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    2 * (a + b + c) + 9 / (a * b + b * c + c * a) ^ 2 ≥ 7 := by
  have h10 : 0 < a * b := by nlinarith
  have h11 : 0 < b * c := by nlinarith
  have h12 : 0 < c * a := by nlinarith
  have h5 : 0 < a * b + b * c + c * a := by positivity
  have h6 : 0 < (a * b + b * c + c * a) ^ 2 := by positivity
  have h7 : 2 * (a + b + c) + 9 / (a * b + b * c + c * a) ^ 2 - 7 ≥ 0 := by
    have h8 : 2 * (a + b + c) + 9 / (a * b + b * c + c * a) ^ 2 - 7 =
        (2 * (a + b + c) * (a * b + b * c + c * a) ^ 2 + 9 - 7 * (a * b + b * c + c * a) ^ 2) / ( (a * b + b * c + c * a) ^ 2 ) := by
      field_simp
      <;> ring
    rw [h8] at *
    apply div_nonneg
    · -- Show the numerator is non-negative
      have h10 : a * b * c = 1 := habc
      nlinarith [sq_nonneg (a + b + c - 3), sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    · -- Show the denominator is positive
      positivity
  linarith