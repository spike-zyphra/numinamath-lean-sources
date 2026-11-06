import Mathlib

theorem number_theory_155109 :
    IsGreatest {A : ℕ | A ∈ Finset.Icc 100000 999999 ∧ 19 ∣ A ∧ 17 ∣ (A / 10) ∧ 13 ∣ (A / 100)} 998412 := by
  constructor
  · -- Show that 998412 is in the set
    constructor
    · norm_num [Finset.mem_Icc]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 998412 is greatest in the set
    intro A h
    rcases h with ⟨hA, h19, h17, h13⟩
    rw [Finset.mem_Icc] at hA
    rcases hA with ⟨hA1, hA2⟩
    by_contra h'
    push_neg at h'
    interval_cases A <;> norm_num at h19 h17 h13 <;> all_goals omega