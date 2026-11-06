import Mathlib

theorem inequalities_319432 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b^2 + b * c + c^2) * (c^2 + c * a + a^2) * (a^2 + a * b + b^2) ≥
    (1 / 3) * (b * c + c * a + a * b)^2 * (2 * (a^2 + b^2 + c^2) + b * c + c * a + a * b) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < c * a from by nlinarith), 
          mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith), 
          sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a)
          ]