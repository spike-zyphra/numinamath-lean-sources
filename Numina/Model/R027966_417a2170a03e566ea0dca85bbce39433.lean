import Mathlib

theorem algebra_20133 {n : ℤ} (hn : n ≠ 0) (h : -10 * n = 10 * (1001 - n)) :
    n = 575 := by
  linarith