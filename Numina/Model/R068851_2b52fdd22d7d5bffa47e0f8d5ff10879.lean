import Mathlib

theorem inequalities_2886 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥
    a * b * c * (a + 2 * b + c) * (2 * a + b + c) * (a + b + 2 * c) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
            sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            mul_pos (show 0 < a from ha) (show 0 < b * c by positivity),
            mul_pos (show 0 < b from hb) (show 0 < a * c by positivity),
            mul_pos (show 0 < c from hc) (show 0 < a * b by positivity),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith)]