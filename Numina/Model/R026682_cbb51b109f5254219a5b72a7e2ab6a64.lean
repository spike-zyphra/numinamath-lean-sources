import Mathlib

open Real

theorem inequalities_603555 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ a * b * c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ sqrt 3 * a * b * c := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b + c - a * b * c), sq_nonneg ((a * b * c) ^ 2 - 3 * (a * b * c) * sqrt 3 / 3),
            Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            sq_nonneg (a * b * c - (a + b + c)), sq_nonneg ((a * b * c) ^ 2 - 3),
            mul_pos (show (0 : ℝ) < sqrt 3 by positivity) (show (0 : ℝ) < a * b * c by positivity)]