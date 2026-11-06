import Mathlib

theorem algebra_8017 {n : ℕ} (hn : n > 0) (h1 : n - 5 + 2 + n / 2 = n + 2) (h2 : n + 2 + 5 - n / 2 = n) :
    n = 10 ∨ n = 8 := by 
  omega