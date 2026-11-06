import Mathlib

theorem number_theory_604197 (n : ℕ) (h : n = 2021) :
    35 ∣ 3^(2*n + 1) + 2^(n + 2) := by
  subst h
  norm_num