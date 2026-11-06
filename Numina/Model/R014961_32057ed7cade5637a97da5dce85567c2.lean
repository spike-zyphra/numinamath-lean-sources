import Mathlib

open Real
open scoped BigOperators

theorem inequalities_250368 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^4 + b^4 + c^4 - 2*(a^2 * b^2 + a^2 * c^2 + b^2 * c^2) +
  a^2 * b * c + b^2 * a * c + c^2 * a * b ≥ 0 := by
  have h1 : 0 < a + b - c := by linarith
  have h2 : 0 < a + c - b := by linarith
  have h3 : 0 < b + c - a := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
    mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
    mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
    mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
  ]