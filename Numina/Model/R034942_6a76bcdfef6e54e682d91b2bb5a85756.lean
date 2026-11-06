import Mathlib

theorem algebra_93488 {n : ℕ} (hn : n = 8 ^ 2022) : n / 4 = 4 ^ 3032 := by
  rw [hn]
  norm_num