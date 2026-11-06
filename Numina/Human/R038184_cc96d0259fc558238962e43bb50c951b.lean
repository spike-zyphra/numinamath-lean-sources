import Mathlib

theorem inequalities_195568 (a b : ℝ) (ha : a < 1) (hb : b < 1)
    (h : a + b ≥ 0.5) : (1 - a) * (1 - b) ≤ 9 / 16 := by 
  have ha' : a ≤ 1 := by linarith
  have hb' : b ≤ 1 := by linarith
  nlinarith [sq_nonneg (a - 0.5), sq_nonneg (b - 0.5), sq_nonneg (a - b)]