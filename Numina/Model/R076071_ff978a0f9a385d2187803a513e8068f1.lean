import Mathlib

theorem algebra_146318 {n : ℕ} (hn : n > 0) (h : n + 10 = (n + 1) * (n + 9)) :
    n = 9 := by
  nlinarith