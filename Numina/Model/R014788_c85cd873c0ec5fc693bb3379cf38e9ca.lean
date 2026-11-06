import Mathlib

theorem inequalities_38121 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / b + b / c + c / a ≥ (a ^ 2 + 1) / (2 * a) + (b ^ 2 + 1) / (2 * b) +
    (c ^ 2 + 1) / (2 * c) := by
  have h1 : a / b + b / c + c / a - ((a ^ 2 + 1) / (2 * a) + (b ^ 2 + 1) / (2 * b) + (c ^ 2 + 1) / (2 * c)) ≥ 0 := by
      have h2 : 0 < a * b * c := by 
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h3 : 2 * a * b * c > 0 := by 
        nlinarith
      have h4 : a / b + b / c + c / a - ((a ^ 2 + 1) / (2 * a) + (b ^ 2 + 1) / (2 * b) + (c ^ 2 + 1) / (2 * c)) =
          (2 * a^2 * c + 2 * a * b^2 + 2 * b * c^2 - (a^2 * b * c + b * c + b^2 * a * c + a * c + c^2 * a * b + a * b)) / (2 * a * b * c) := by 
        field_simp
        ring
      rw [h4] 
      apply div_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * (b - 1)), sq_nonneg (b * (c - 1)), sq_nonneg (c * (a - 1)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      positivity 
  linarith