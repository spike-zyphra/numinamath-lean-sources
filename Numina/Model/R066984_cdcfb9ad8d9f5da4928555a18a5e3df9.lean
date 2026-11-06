import Mathlib

theorem number_theory_201804 {n : ℕ} (hn : n > 0) (h : 7 * n + 1 = 2 * (7 * (n - 1) + 1)) :
    n = 1166666 := by
  omega