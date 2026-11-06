import Mathlib

theorem inequalities_327475 {a b : ℝ} (ha : 0 < b) (hb : b < a)
    (h1 : a + b ≥ 5 / 9) (h2 : a * b ≤ 4 / 81) :
    a ≥ 4 / 9 := by 
  nlinarith [sq_nonneg (a - 4 / 9), sq_nonneg (b - 1 / 9),
    mul_pos (show 0 < b by linarith) (show 0 < a by nlinarith),
    sq_nonneg (a * b - 4 / 81), sq_nonneg (a + b - 5 / 9)]