import Mathlib

theorem inequalities_599163 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    a + b + c ≥ 2 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
    h, 
    sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4),
    mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith),
    mul_pos (show 0 < a * c by nlinarith) (show 0 < b by linarith),
    mul_pos (show 0 < b * c by nlinarith) (show 0 < a by linarith)]