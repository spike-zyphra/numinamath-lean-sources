import Mathlib

theorem number_theory_12207 (total remaining : ℕ) (htotal : total = 8 * 42 * 6)
    (hremaining : 4 * 42 * 10 + 33 * 10 + remaining = total) : remaining = 6 := by
  subst htotal
  omega