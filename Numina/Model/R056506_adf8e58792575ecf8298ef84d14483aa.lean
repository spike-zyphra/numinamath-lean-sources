import Mathlib

theorem number_theory_233840 : ∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x * 5 = y * 73 := by 
  exact ⟨73, 5, by norm_num, by norm_num, by norm_num⟩