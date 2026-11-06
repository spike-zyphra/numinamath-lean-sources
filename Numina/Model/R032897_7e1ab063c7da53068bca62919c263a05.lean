import Mathlib

theorem inequalities_70890 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a - 1) / c + (c - 1) / b + (b - 1) / a ≥ 0 := by
  have h2 : (a - 1) / c + (c - 1) / b + (b - 1) / a = 
    (a ^ 2 * b + b ^ 2 * c + a * c ^ 2 - (a * b + a * c + b * c)) / (a * b * c) := by
    field_simp
    <;> ring
  rw [h2]
  apply div_nonneg
  · -- Show that the numerator is non-negative
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
      ]
  · -- Show that the denominator is positive
    nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]