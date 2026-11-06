import Mathlib

open Real
open scoped BigOperators

theorem inequalities_281410 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^3 + b^3 + 3 * a * b * c > c^3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (a + b - c),
          sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')]