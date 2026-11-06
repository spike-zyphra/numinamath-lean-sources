import Mathlib

theorem inequalities_603603 {a b c : ℝ} (ha : a > b) (hb : b > c) (h : a + b + c = 1) (h' : a^2 + b^2 + c^2 = 3) :
    b + c < 1 / 2 := by
  nlinarith [sq_pos_of_pos (show (0 : ℝ) < a - b by linarith), sq_pos_of_pos (show (0 : ℝ) < b - c by linarith), sq_nonneg (a - b), sq_nonneg (b - c)]