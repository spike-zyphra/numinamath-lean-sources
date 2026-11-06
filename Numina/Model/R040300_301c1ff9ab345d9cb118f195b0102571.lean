import Mathlib

theorem inequalities_37223 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a^2 + a * b + b^2 = 3 * c^2) (h2 : a^3 + a^2 * b + a * b^2 + b^3 = 4 * d^3) :
    a + b + d ≤ 3 * c := by

  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c), sq_nonneg (d - (a + b) / 2), sq_nonneg (c - (a + b) / 2),
          sq_nonneg (d - c), sq_nonneg (a + b - 2 * d), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
          mul_pos hc hd]