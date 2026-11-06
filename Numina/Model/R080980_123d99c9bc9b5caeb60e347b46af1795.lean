import Mathlib

open Real
open scoped BigOperators

theorem inequalities_161716 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  2 * (a^2 + b^2) > c^2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (a + b - c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]