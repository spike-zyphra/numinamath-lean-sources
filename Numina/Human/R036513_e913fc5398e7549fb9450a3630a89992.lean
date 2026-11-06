import Mathlib

theorem inequalities_598955 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a^3 + b^3 = 2) : a + b ≤ 2 := by
  have h1 : a + b ≤ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h, mul_pos ha hb, sq_nonneg (a - 1), sq_nonneg (b - 1)]
  exact h1