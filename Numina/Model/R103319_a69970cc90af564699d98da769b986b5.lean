import Mathlib

theorem number_theory_13766 {n : ℕ} (hn : n = 32768) :
    (n / 1000) ^ 3 = n := by
  subst hn
  norm_num