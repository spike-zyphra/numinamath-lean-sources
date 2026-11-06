import Mathlib

theorem number_theory_169397 {n : ℕ} (hn : n > 0) (h : n / 10 = 100 * (n - 1) / 100 + n) :
    n = 40 := by
  omega