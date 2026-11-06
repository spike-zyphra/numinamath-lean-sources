import Mathlib

open Real
open scoped BigOperators

theorem inequalities_141416 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^2 + b^2 + c^2 < 2 * (a * b + b * c + a * c) := by

  have h1 : a ^ 2 + b ^ 2 + c ^ 2 - 2 * (a * b + b * c + a * c) < 0 := by
    have h2 : (b + c - a) ^ 2 < 4 * b * c := by
      have h3 : a < b + c := by linarith
      have h4 : 0 < b + c - a := by linarith
      have h5 : (a) ^ 2 > (b - c) ^ 2 := by
        have h6 : a > b - c := by
          linarith
        have h7 : a > c - b := by
          linarith
        have h8 : a ^ 2 > (b - c) ^ 2 := by
          nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
        linarith
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - (b + c)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h3 : a ^ 2 + b ^ 2 + c ^ 2 - 2 * (a * b + b * c + a * c) = (b + c - a) ^ 2 - 4 * b * c := by
      nlinarith
    have h9 : (b + c - a) ^ 2 - 4 * b * c < 0 := by
      nlinarith
    linarith [h3, h9]
  linarith [h1]