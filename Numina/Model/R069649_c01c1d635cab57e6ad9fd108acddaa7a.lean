import Mathlib

theorem inequalities_201727 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 - a * b = c^2) : (a - c) * (b - c) ≤ 0 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a - c), sq_nonneg (b - c)]