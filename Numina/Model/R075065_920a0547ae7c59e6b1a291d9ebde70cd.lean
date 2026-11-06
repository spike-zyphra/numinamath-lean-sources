import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600547 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 * b + b^2 * c + c^2 * a ≤ (a + b + c)^3 / 8 - 3 / 8 * (-a + b + c) * (-b + a + c) * (-c + a + b) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
          --, mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)
          ]