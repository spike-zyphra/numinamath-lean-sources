import Mathlib

theorem number_theory_14755 (total_lollipops : ℕ) (h : total_lollipops = 45 + 116 + 4 + 229) (n : ℕ) (hn : n = 11) :
    total_lollipops % n = 9 := by
  subst hn
  subst h
  all_goals norm_num