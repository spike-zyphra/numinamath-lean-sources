import Mathlib

theorem inequalities_86430 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = a + b + c + 2) :
    (a + 1) * (b + 1) * (c + 1) ≥ 27 := by
  nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
          sq_nonneg (a * b - 4), sq_nonneg (a * c - 4), sq_nonneg (b * c - 4),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h]