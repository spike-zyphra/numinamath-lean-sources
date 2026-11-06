import Mathlib

theorem number_theory_81079 {n : ℕ} (h : 3 * n = 999 ^ 1000) :
    n % 10 = 7 := by
  omega