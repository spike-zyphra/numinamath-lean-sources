import Mathlib

theorem algebra_324113 {n : ℕ} (hn : n > 0) (h1 : n % 15 = n % 13 + 1) (h2 : (n + 1) % 15 = (n + 1) % 13) :
    n = 184 := by
  omega