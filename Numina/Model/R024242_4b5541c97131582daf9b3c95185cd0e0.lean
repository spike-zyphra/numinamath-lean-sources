import Mathlib

theorem number_theory_109516 : ∃ d1 d2, d1 < 10 ∧ d2 < 10 ∧ 45 ∣ (520000 + 10000 * d1 + 1000 * d2) := by
  use 2, 0
  all_goals norm_num