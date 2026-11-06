import Mathlib

open Real

theorem inequalities_225682 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c * (a + b + c) = a * b + b * c + c * a) :
    5 * (a + b + c) ≥ 7 + 8 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a + b + c - 3), sq_nonneg (a * b * c - 1),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_pos (show 0 < a * b by positivity) (show 0 < c by assumption),
    sq_nonneg (a * b * c),
    mul_pos (mul_pos ha hb) hc,
    sq_nonneg ((a + b + c) - 3)
  ]