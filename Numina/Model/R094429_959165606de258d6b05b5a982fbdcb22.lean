import Mathlib

open Real
open scoped BigOperators

theorem inequalities_99865 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a^2 + b^2 + c^2 < 2 * (a * b + b * c + c * a) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
      mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith),
      mul_pos (show 0 < c + a - b by linarith) (show 0 < a + b - c by linarith)]