import Mathlib

theorem inequalities_60160 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a * b * c * d = 1) :
    10 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + a * b + a * c + a * d + b * c + b * d + c * d := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (a * d - 1), 
          sq_nonneg (b * c - 1), sq_nonneg (b * d - 1), sq_nonneg (c * d - 1),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, 
          mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd]