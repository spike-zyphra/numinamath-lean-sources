import Mathlib

theorem number_theory_138811 {n : ℕ} (hn : n > 0) (h : n + (n + 1) = 21) :
    n * (n + 1) = 110 := by
  have hn10 : n = 10 := by
    omega
  subst hn10
  all_goals norm_num