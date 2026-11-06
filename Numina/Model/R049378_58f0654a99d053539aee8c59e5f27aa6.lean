import Mathlib

theorem number_theory_220768 : ∃ x, x % 17 = 15 ∧ x % 13 = 11 ∧ x % 10 = 3 := by
  exact ⟨1103, by norm_num, by norm_num, by norm_num⟩