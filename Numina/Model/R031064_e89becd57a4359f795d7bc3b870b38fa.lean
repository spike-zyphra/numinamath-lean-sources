import Mathlib

theorem inequalities_109754 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≤ a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 := by
  have h1 : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 - (a / b + b / c + c / a) ≥ 0 := by 
    have h2 : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 - (a / b + b / c + c / a) = 
      (a ^ 4 * c ^ 2 + b ^ 4 * a ^ 2 + c ^ 4 * b ^ 2 - a^3 * b * c^2 - b^3 * c * a^2 - c^3 * a * b^2) / (a^2 * b^2 * c^2) := by
      field_simp
      ring 
    rw [h2]
    apply div_nonneg 
    nlinarith [sq_nonneg (a^2 * c - b^2 * a), sq_nonneg (b^2 * a - c^2 * b), sq_nonneg (c^2 * b - a^2 * c), 
      sq_nonneg (a^2 * c - a * b * c), sq_nonneg (b^2 * a - a * b * c), sq_nonneg (c^2 * b - a * b * c), 
      sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    all_goals positivity
  linarith [h1]