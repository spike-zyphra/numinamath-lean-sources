import Mathlib

theorem inequalities_207308 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + b < c + d) (h2 : (a + b) * (c + d) < a * b + c * d) (h3 : (a + b) * c * d < a * b * (c + d)) :
    False := by
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
          mul_self_nonneg (a - b), mul_self_nonneg (c - d),
          mul_self_nonneg (a + b - c - d)]