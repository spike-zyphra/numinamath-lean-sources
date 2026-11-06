import Mathlib

theorem inequalities_195568 (a b : ℝ) (ha : a < 1) (hb : b < 1)
    (h : a + b ≥ 0.5) : (1 - a) * (1 - b) ≤ 9 / 16 := by
  have h1 : a < 1 := by linarith
  have h2 : b < 1 := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 0.5), sq_nonneg (a - 0.25), sq_nonneg (b - 0.25), mul_pos (sub_pos.mpr (show (1:ℝ) > a by linarith)) (sub_pos.mpr (show (1:ℝ) > b by linarith)), sq_nonneg (a + b - 1), mul_self_nonneg (a - b)]