import Mathlib

theorem inequalities_598880 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^2 + b^2 + c^2 = 3) :
    12 + 9 * a * b * c ≥ 7 * (a * b + b * c + a * c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b + c - 3), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]