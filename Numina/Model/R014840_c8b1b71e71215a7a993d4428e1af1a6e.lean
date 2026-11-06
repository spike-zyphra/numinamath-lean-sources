import Mathlib

theorem number_theory_111198 {n : ℕ} (h : n = 2178) :
    n = (1000 * (n % 10) + 100 * ((n / 10) % 10) +
          10 * ((n / 100) % 10) + (n / 1000)) / 4 := by
  subst h
  norm_num