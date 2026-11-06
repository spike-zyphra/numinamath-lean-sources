import Mathlib

theorem number_theory_285722 : ∃ n, n % 7 = 4 ∧ n = 18 := by 
  exact ⟨18, by norm_num, rfl⟩