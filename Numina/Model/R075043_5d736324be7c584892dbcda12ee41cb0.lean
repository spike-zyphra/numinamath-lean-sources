import Mathlib

theorem number_theory_65894 :
    IsLeast {m : ℕ | 0 < m ∧ 79 ∣ m ^ 3 - 3 * m ^ 2 + 2 * m ∧ 83 ∣ m ^ 3 - 3 * m ^ 2 + 2 * m} 1660 := by
  constructor
  · -- First prove that 1660 is in the set
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  · -- Now prove minimality: there is no smaller element in the set
    intro m hm
    rcases hm with ⟨hm_pos, hm_79, hm_83⟩
    by_contra h
    push_neg at h
    interval_cases m <;> norm_num at hm_79 hm_83 <;> omega