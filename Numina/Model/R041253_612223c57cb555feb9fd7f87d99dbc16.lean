import Mathlib

theorem inequalities_601803 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 4) :
    a^3 + b^3 + c^3 + d^3 + 10 * (a * b + b * c + c * d + d * a + a * c + b * d) ≤ 64 := by
  have h1 : a + b + c + d = 4 := h
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a + b + c + d - 4), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd]