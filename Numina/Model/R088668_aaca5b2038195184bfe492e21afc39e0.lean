import Mathlib

theorem algebra_3100 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (habc : a * b * c = 1) :
    a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) = 1 := by
  have h2 : a * b + a + 1 ≠ 0 := by
    positivity

  have h3 : b * c + b + 1 ≠ 0 := by
    positivity

  have h4 : c * a + c + 1 ≠ 0 := by
    positivity
  
  field_simp [h2, h3, h4] at *
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]