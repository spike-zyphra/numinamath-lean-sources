import Mathlib

open Real

theorem algebra_602122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    1 / a^2 + 1 / b^2 + 1 / c^2 - 2 * (a^3 + b^3 + c^3) / (a * b * c) ≥ 3 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 1 / a^2 + 1 / b^2 + 1 / c^2 - 2 * (a^3 + b^3 + c^3) / (a * b * c) - 3 ≥ 0 := by
    have h4 : a^2 * b^2 * c^2 > 0 := by positivity
    have h5 : (1 / a^2 + 1 / b^2 + 1 / c^2 - 2 * (a^3 + b^3 + c^3) / (a * b * c) - 3) = 
      (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - 2 * (a^3 + b^3 + c^3) * (a * b * c) - 3 * a^2 * b^2 * c^2) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
      ]
    all_goals positivity
  linarith