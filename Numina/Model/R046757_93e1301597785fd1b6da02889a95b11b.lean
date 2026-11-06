import Mathlib

theorem inequalities_597278 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    6 * (a^2 + b^2 + c^2 + d^3) ≥ (a^2 + b^2 + c^2 + d^2) + 1 / 8 := by
  have h1 : a + b + c + d = 1 := h
  nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4),
          sq_nonneg (d - 1 / 4), sq_nonneg (d^2), sq_nonneg (d * (d - 1 / 4)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]