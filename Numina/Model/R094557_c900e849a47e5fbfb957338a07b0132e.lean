import Mathlib

open Real

theorem inequalities_221039 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 ≤ 3 * (a + b + c)^3 - 26 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - a - b - c), sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b + c - c by nlinarith) (show 0 < a + b + c - b - c by nlinarith),
          mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), 
          sq_nonneg (a + b + c - c), sq_nonneg (b + c), sq_nonneg (c + b), sq_nonneg (a + b + c - a - b - c), 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ b * c by nlinarith), 
          mul_nonneg (show 0 ≤ b * c by nlinarith) (show 0 ≤ c * a by nlinarith),
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ c * a by nlinarith)
          ]