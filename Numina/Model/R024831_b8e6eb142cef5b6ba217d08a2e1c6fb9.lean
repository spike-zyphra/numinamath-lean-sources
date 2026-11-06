import Mathlib

theorem inequalities_5019 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a * b + a * c + a * d + b * c + b * d + c * d = 6) :
    a^2 + b^2 + c^2 + d^2 + 2 * a * b * c * d ≥ 6 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]