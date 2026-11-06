import Mathlib

theorem number_theory_154857 :
    ∃ a b, a % (b + 1) = 0 ∧ 43 % (a + b) = 0 := by 
  exact ⟨42, 1, by norm_num, by norm_num⟩