import Mathlib

theorem algebra_20964 (n : ℕ) (h : n + (n + 1) + (n + 2) + (n + 3) + (n + 4) = 105) :
    (n + 2) - ((n + n + 1 + n + 2 + n + 3 + n + 4) / 5 : ℝ) = 0 := by
  have hn : n = 19 := by
    omega
  rw [hn]
  norm_num