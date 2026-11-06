import Mathlib

theorem inequalities_7900 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c * (a + b + c) = 1) :
    9 * (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥
    (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 +
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b * c - 1 / (a + b + c)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (show 0 < a + b + c by positivity) (show 0 < a * b * c by positivity)
          ]