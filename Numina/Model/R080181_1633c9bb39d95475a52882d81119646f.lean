import Mathlib

theorem number_theory_129907 : ∃ x y, 3 ∣ x ∧ 3 ∣ y ∧ x^2 + y^2 = 450 := by 
  exact ⟨3, 21, by norm_num, by norm_num, by norm_num⟩