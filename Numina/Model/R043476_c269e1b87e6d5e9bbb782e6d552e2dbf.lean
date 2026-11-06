import Mathlib

theorem inequalities_7198 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * b^2 + b^4 * c^2 + c^4 * a^2 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a^3 + b^3 + c^3) := by 
  nlinarith [sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c), 
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), sq_nonneg (a * (a - c)), sq_nonneg (c * (c - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (mul_pos ha hb) hc
          ]