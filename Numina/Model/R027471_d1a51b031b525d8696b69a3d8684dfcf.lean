import Mathlib

open Real
open scoped BigOperators

theorem inequalities_66653
  (a b c p q r : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hp : p + q + r = 0)
  (h : a + b > c)
  (h' : a + c > b)
  (h'' : b + c > a) :
  a^2 * p * q + b^2 * q * r + c^2 * r * p ≤ 0 := by
  have hr : r = -p - q := by linarith
  rw [hr]
  have h10 : -2 * b * c < a ^ 2 - b ^ 2 - c ^ 2 := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h11 : a ^ 2 - b ^ 2 - c ^ 2 < 2 * b * c := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h12 : (a ^ 2 - b ^ 2 - c ^ 2) ^ 2 < 4 * b ^ 2 * c ^ 2 := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  nlinarith [sq_nonneg (2 * b * q - 2 * c * p), sq_nonneg (2 * b * c * p - (a ^ 2 - b ^ 2 - c ^ 2) * p), sq_nonneg (2 * b * c * q - (a ^ 2 - b ^ 2 - c ^ 2) * p), sq_nonneg (b * q - c * p), sq_nonneg (b * q + c * p), sq_nonneg (a ^ 2 - b ^ 2 - c ^ 2) ]