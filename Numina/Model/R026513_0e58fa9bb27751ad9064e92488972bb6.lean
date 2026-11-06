import Mathlib

theorem number_theory_199366 (d : ℕ) (hd : d > 0) (hne2 : d ≠ 2) (hne5 : d ≠ 5) (hne13 : d ≠ 13) :
    ∃ a b, (a = 2 ∧ b = 5) ∨ (a = 2 ∧ b = 13) ∨ (a = 5 ∧ b = 13) ∨ (a = d ∧ b = 2) ∨
            (a = d ∧ b = 5) ∨ (a = d ∧ b = 13) ∧ ¬ ∃ m, m^2 = a * b - 1 := by
  use 2, 5
  left
  all_goals
    tauto