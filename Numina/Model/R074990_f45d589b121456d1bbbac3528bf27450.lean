import Mathlib

open Real
open scoped BigOperators

theorem inequalities_215671 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 + 4 * a * b * c > a^3 + b^3 + c^3 := by

  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (sub_pos.2 h) (sub_pos.2 h'), 
          mul_pos (sub_pos.2 h) (sub_pos.2 h''), 
          mul_pos (sub_pos.2 h') (sub_pos.2 h''), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)
          ]