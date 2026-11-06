import Mathlib

theorem number_theory_119312 {n : ℕ} (hn : n < 50) (h1 : n % 8 = 2) (h2 : n % 12 = 6) :
    n ≤ 42 := by
  omega