import Mathlib

open Real
open scoped BigOperators

theorem inequalities_156838 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^4 + b^4 + c^4 < 2 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) := by 
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')]