import Mathlib

theorem inequalities_307749 {a b c : ℝ} (ha : a > b) (hb : b > c) (h1 : a + b + c = 1)
    (h2 : a^2 + b^2 + c^2 = 3) :
    -2 / 3 < b + c ∧ b + c < 1 / 2 := by
  constructor
  · -- Prove -2/3 < b + c
    nlinarith [sq_pos_of_pos (show 0 < a - b by linarith), sq_pos_of_pos (show 0 < b - c by linarith),
      sq_nonneg (a - 1 + (b + c)), sq_nonneg (a - (b + c) / 2), sq_nonneg (b - c)]
  · -- Prove b + c < 1/2
    nlinarith [sq_pos_of_pos (show 0 < a - b by linarith), sq_pos_of_pos (show 0 < b - c by linarith),
      sq_nonneg (a - 1 + (b + c)), sq_nonneg (a - (b + c) / 2), sq_nonneg (b - c)]