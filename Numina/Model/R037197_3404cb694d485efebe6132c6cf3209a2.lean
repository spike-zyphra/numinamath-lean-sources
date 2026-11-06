import Mathlib

theorem inequalities_601282 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 ≤ c / a + a / (b + c) + b / c := by 
  have h1 : 0 < a * (b + c) * c := by 
    positivity
  have h2 : c / a + a / (b + c) + b / c - 2 ≥ 0 := by 
    have h3 : c / a + a / (b + c) + b / c - 2 = (c ^ 2 * (b + c) + a ^ 2 * c + a * b * (b + c) - 2 * a * (b + c) * c) / (a * (b + c) * c) := by
      field_simp 
      ring
    rw [h3] 
    apply div_nonneg
    -- Show that the numerator is non-negative
    nlinarith [sq_nonneg (c - a), sq_nonneg (b - c), sq_nonneg (a - (b + c)), 
      sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (c - (b + c)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    -- Show that the denominator is positive
    positivity
  linarith