import Mathlib

open Real
open scoped BigOperators

theorem inequalities_86339 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  (a + b) * (b + c) * (c + a) ≥ 8 * (a + b - c) * (b + c - a) * (c + a - b) := by

  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)]