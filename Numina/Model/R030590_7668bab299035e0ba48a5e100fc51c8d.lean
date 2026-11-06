import Mathlib

theorem inequalities_234925 {a b : ℝ} (ha : a < 1) (hb : b < 1) (h : a + b ≥ 1 / 3) :
    (1 - a) * (1 - b) ≤ 25 / 36 := by
  nlinarith [sq_nonneg (a - 1 / 6), sq_nonneg (b - 1 / 6), sq_nonneg (a - b), 
    mul_pos (sub_pos.mpr (show a < 1 by linarith)) (sub_pos.mpr (show b < 1 by linarith)), 
    sq_nonneg (a + b - 2 / 3)]