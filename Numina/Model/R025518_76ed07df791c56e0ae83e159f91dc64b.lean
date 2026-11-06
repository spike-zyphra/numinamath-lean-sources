import Mathlib

theorem inequalities_30823 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≤
    (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by 
  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < b * c := by nlinarith
  have h3 : 0 < c * a := by nlinarith
  have h6 : 0 < (a + b) * (b + c) * (c + a) := by positivity
  have h7 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 ≤ 0 := by
    have h8 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 =
        ( (b + c) * (c + a) * 2 + (a + b) * (c + a) * 2 + (a + b) * (b + c) * 2 - (a ^ 2 + b ^ 2 + c ^ 2) * (a + b) * (b + c) * (c + a) ) / ( (a + b) * (b + c) * (c + a) * 2 ) := by
      field_simp
      ring
    rw [h8]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0.
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc
      ]
    · -- Show that the denominator is ≥ 0.
      positivity
  linarith