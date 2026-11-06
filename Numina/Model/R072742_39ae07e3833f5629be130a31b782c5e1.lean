import Mathlib

theorem inequalities_5311 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (lambda : ℝ) (hl : 0 ≤ lambda) :
    (a + b + lambda) * (b + c + lambda) * (c + a + lambda) ≥ (2 * a + lambda) * (2 * b + lambda) * (2 * c + lambda) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b - c - lambda), sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ lambda by linarith),
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ lambda by linarith),
            mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ lambda by linarith)]