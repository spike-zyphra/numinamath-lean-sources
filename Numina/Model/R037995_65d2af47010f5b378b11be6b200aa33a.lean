import Mathlib

theorem inequalities_147164 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b * c ≥ (a + b - c) * (b + c - a) * (c + a - b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
    mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith),
    mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < c by linarith),
    mul_pos (show (0 : ℝ) < c by linarith) (show (0 : ℝ) < a by linarith)
  ]