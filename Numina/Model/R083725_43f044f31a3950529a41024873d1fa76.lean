import Mathlib

theorem number_theory_166126 : ∃ n, n % 6 = 0 ∧ n % 7 = 0 ∧ n % 9 = 0 ∧ n = 41832 := by
  use 41832
  all_goals norm_num