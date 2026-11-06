import Mathlib

theorem number_theory_13049 {n : ℕ} (hn : n % 77 = 12) (h : n % 91 = 54) :
    n % 143 = 67 := by
  omega