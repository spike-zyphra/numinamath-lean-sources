import Mathlib

theorem number_theory_222874 (n : ℕ) :
    ∃ x y, n ∣ x^2 + y^2 - 2017 := by
  use 44, 9
  all_goals norm_num