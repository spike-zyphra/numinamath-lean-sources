import Mathlib

theorem inequalities_216054 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d = 1) :
    |a * b - c * d| ≤ 1 / 4 := by
  have h1 : -1 / 4 ≤ a * b - c * d := by
    nlinarith [sq_nonneg (a + b - c - d), sq_nonneg (a - b), sq_nonneg (c - d),
              hsum, mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd]
  have h2 : a * b - c * d ≤ 1 / 4 := by
    nlinarith [sq_nonneg (a + b - c - d), sq_nonneg (a - b), sq_nonneg (c - d),
              hsum, mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd]
  apply abs_le.mpr
  constructor
  · linarith [h1]
  · linarith [h2]