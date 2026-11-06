import Mathlib

open Real
open scoped BigOperators

theorem inequalities_169680 {a b c : ℝ}
    (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) (h1 : a > b) :
    a + b / 2 > c ∧ c > 8 / 9 * (a + b / 2) := by
  have h2 : a + b / 2 > c := by
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - b), mul_pos ha hb, h1, sq_nonneg (c - (a + b / 2)), h, sq_nonneg (c - a), sq_nonneg (a - b), sq_nonneg (c - b)]
  have h3 : c > 8 / 9 * (a + b / 2) := by
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - b), sq_nonneg (c - a), sq_nonneg (b - a / 2), mul_pos ha hb, h1, sq_nonneg (c^2 - (a^2 + b^2)), sq_nonneg (a - 2 * b), sq_nonneg (a - 3 * b), sq_nonneg (a - b), sq_nonneg (2 * a - 3 * b), sq_nonneg (b), sq_nonneg (a - 2 * c), sq_nonneg (a^2 + b^2 - 4 * c^2)]
  constructor
  · exact h2
  · exact h3