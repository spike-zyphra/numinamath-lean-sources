import Mathlib

theorem number_theory_599818 (d : ℕ) (hd : d > 0) (hne2 : d ≠ 2) (hne5 : d ≠ 5) (hne13 : d ≠ 13) :
    ∃ a b, (a = 2 ∧ b = 5) ∨ (a = 2 ∧ b = 13) ∨ (a = 5 ∧ b = 13) ∨ (a = 2 ∧ b = d) ∨
    (a = 5 ∧ b = d) ∨ (a = 13 ∧ b = d) ∧ ¬ ∃ m, m^2 = a * b - 1 := by 
  use 2, 5
  left
  all_goals
    simp
    all_goals
      try { tauto }