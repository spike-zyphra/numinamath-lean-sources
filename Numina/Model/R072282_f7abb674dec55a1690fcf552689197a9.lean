import Mathlib

theorem number_theory_306090 : ∃ n m, n > 0 ∧ m > 0 ∧ (n - 1) * 5 + m = 2007 := by
  exact ⟨402, 2, by norm_num, by norm_num, by norm_num⟩