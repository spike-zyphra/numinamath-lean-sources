import Mathlib

theorem number_theory_101713 : ∃ n m, n > 0 ∧ m > 0 ∧ (n * (n - 1) / 2 + m) = 2015 := by
  exact ⟨63, 62, by norm_num, by norm_num, by norm_num⟩