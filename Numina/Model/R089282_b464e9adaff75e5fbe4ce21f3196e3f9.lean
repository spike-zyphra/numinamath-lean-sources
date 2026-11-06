import Mathlib

theorem algebra_196793 (n : ℕ) (h : n > 0) (h1 : n % 2 = 0) (h2 : n % 3 = 0)
    (h3 : n / 2 = n / 3 + 1) (h4 : n / 3 = n / 2 + 2) :
    n = 6 := by
  omega