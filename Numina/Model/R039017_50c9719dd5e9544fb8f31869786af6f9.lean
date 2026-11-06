import Mathlib

theorem number_theory_35225 : ∃ k, 3^2008 ∣ k^3 - 36 * k^2 + 51 * k - 97 := by
  use 0
  all_goals
    norm_num