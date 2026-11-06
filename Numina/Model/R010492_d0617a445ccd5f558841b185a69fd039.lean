import Mathlib

theorem number_theory_14623 :
    IsLeast {x | 0 < x ∧ 23 ∣ x ∧ ∃ k, x = 89 * k + 4} 805 := by 
  constructor
  · -- Verify 805 is in the set
    refine' ⟨by norm_num, by norm_num, ⟨9, by norm_num⟩⟩

  · -- Now we need to show that 805 is the smallest such
    intro y hy
    rcases hy with ⟨hy_pos, hy_div_23, ⟨k, hy_eq⟩⟩

    omega