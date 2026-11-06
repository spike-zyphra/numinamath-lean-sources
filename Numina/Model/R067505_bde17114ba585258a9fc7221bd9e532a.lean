import Mathlib

theorem inequalities_129956 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + b < c + d) (h2 : (a + b) * (c + d) < a * b + c * d) (h3 : (a + b) * c * d < (c + d) * a * b) :
    False := by
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
          sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d)]