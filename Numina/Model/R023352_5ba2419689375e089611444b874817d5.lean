import Mathlib

theorem number_theory_260596 (n : ℕ) (h : n > 0) (h1 : n % 2 = 1) (h2 : n % 3 = 2)
    (h3 : n % 4 = 5) (h4 : n % 5 = 4) (h5 : n % 6 = 5) (h6 : n % 7 = 6) :
    n = 839 := by
  omega