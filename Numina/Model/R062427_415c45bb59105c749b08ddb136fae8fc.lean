import Mathlib

open Real
open scoped BigOperators

theorem inequalities_280518 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^2 * (-a + b + c) + b^2 * (a - b + c) + c^2 * (a + b - c) ≤ 3 * a * b * c := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')]