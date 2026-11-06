import Mathlib

open Real

theorem inequalities_126219 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + 1) * (b + 1) * (c + 1) = 8) : a + b + c ≥ 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b + c - 3), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]