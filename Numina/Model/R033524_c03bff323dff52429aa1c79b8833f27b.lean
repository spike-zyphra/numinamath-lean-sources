import Mathlib

open Real
open scoped BigOperators

theorem inequalities_74251 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) +
  2 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) ≥
  5 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (sub_pos.2 h) (sub_pos.2 h'), 
          mul_pos (sub_pos.2 h') (sub_pos.2 h''), 
          mul_pos (sub_pos.2 h'') (sub_pos.2 h)
        ]