import Mathlib

theorem inequalities_225725 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c * (a + b + c) = 3) :
    8 ≤ (a + b) * (b + c) * (c + a) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b * c - 1), sq_nonneg (a + b + c - 3), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (mul_pos ha hb) hc]