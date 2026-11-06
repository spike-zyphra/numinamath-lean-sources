import Mathlib

theorem number_theory_194391 (A : ℕ) (h : A < 10) (total : ℕ)
    (h_total : total = 100 + 10 * A + 2) (h_div : total % 11 = 0) :
    A = 3 := by
  subst h_total
  omega