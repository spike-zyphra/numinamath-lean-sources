import Mathlib

theorem number_theory_257810 :
    IsLeast {a : ℕ | 0 < a ∧ 5 ∣ a ∧ 7 ∣ a + 1 ∧ 9 ∣ a + 2 ∧ 11 ∣ a + 3} 1735 := by
  constructor
  · -- Show 1735 is in the set
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show 1735 is the smallest
    intro a ha
    rcases ha with ⟨ha_pos, ha5, ha7, ha9, ha11⟩
    by_contra h
    push_neg at h
    interval_cases a <;> norm_num at *
    all_goals omega