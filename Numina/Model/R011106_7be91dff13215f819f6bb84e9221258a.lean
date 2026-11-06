import Mathlib
set_option maxHeartbeats 800000
theorem inequalities_614094   (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  9 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤
  8 * (a^3 + b^3 + c^3)^2 := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b) + a * (a - c) + b * (b - a) + b * (b - c) + c * (c - a) + c * (c - b)), 
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
          mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
          mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)]