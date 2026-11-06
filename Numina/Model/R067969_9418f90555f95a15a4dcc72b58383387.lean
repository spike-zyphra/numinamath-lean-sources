import Mathlib

open Real
open scoped BigOperators

theorem inequalities_33297 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
    mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
    mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
    mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)]