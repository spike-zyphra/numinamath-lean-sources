import Mathlib

theorem inequalities_36278 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + a * b + a * c + a * d + b * c + b * d + d * c ≥ 10 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (a * d - 1), sq_nonneg (b * c - 1), sq_nonneg (b * d - 1), sq_nonneg (c * d - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]