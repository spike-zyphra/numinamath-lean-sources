import Mathlib

theorem number_theory_116535 : ∃ m n, (1 / m : ℚ) + (1 / n : ℚ) = 1 / 50 + 1 / 20 := by
  use 50, 20
  all_goals norm_num