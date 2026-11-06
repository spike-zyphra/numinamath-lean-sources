import Mathlib

theorem inequalities_89637 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * b + b * c + c * a + 1) * (a + b) * (b + c) * (c + a) ≥ 2 * a * b * c * (a + b + c + 1) ^ 2 := by
  nlinarith [sq_nonneg (a * b - b * c), 
          sq_nonneg (b * c - c * a), 
          sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), 
          sq_nonneg (b - c), 
          sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b + b * c + c * a - a * b * c), 
          sq_nonneg (a * b + b * c + c * a - (a + b + c)), 
          sq_nonneg (a + b + c - a * b * c)
          ]