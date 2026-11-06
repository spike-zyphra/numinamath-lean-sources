import Mathlib

theorem number_theory_288103 (d : ℕ) (hd : d > 0) (hne2 : d ≠ 2) (hne5 : d ≠ 5) (hne13 : d ≠ 13) :
    ∃ x y, (x = 2 ∧ y = 5) ∨ (x = 2 ∧ y = 13) ∨ (x = 5 ∧ y = 13) ∨ (x = d ∧ y = 2) ∨
    (x = d ∧ y = 5) ∨ (x = d ∧ y = 13) ∧ ¬ ∃ m, m^2 = x * y - 1 := by
  use 2, 5
  left
  all_goals
  constructor
  · rfl
  · rfl