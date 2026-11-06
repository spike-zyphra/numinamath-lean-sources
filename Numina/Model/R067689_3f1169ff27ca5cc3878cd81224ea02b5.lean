import Mathlib

theorem inequalities_126600 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a * b)^2 + (b * c)^2 + (c * a)^2 = 3) :
    (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≥ 1 := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          sq_nonneg (a * (b - 1)), sq_nonneg (b * (c - 1)), sq_nonneg (c * (a - 1)), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]