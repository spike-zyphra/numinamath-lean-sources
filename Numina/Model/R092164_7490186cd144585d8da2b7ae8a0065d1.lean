import Mathlib

theorem algebra_2527 {n : ℝ} (hn : n = 1 + 1 / 3 - 7 / 12 + 9 / 20 - 11 / 30 + 13 / 42 - 15 / 56 + 17 / 72) :
    -1 / n = -9 / 10 := by
  rw [hn]
  norm_num