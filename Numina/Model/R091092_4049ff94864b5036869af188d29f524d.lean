import Mathlib

theorem algebra_143912 {n : ℕ} (hn : n > 0) (h1 : n % 11 = 0) (h2 : (n / 11) * 3 = n / 7) :
    n = 12 ∨ n = 14 ∨ n = 18 ∨ n = 22 ∨ n = 32 := by
  omega