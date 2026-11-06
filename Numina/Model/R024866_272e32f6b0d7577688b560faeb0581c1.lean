import Mathlib

open Real
open scoped BigOperators

theorem inequalities_601159 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
         ]