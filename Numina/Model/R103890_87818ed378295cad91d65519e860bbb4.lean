import Mathlib

theorem inequalities_241601 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 14) :
    14 ≤ a^5 + (1/8)*b^5 + (1/27)*c^5 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3),
          sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 4), sq_nonneg (c^2 - 9),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          pow_two_nonneg (a - 1), pow_two_nonneg (b - 2), pow_two_nonneg (c - 3)
          ]