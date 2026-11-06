import Mathlib

theorem inequalities_599064
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    3 / 2 ≤ a + b + c := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - 3 / 2), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]