import Mathlib

theorem number_theory_3330 :
    IsLeast {x : ℕ | x ∈ Finset.Icc 100 999 ∧ (2 * x - 5) % 19 = 0 ∧ (7 * x - 15) % 23 = 0} 449 := by
  constructor
  · -- Show 449 is in the set
    constructor
    · -- Show 449 is a three-digit number
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Check (2 * 449 - 5) % 19 = 0
      norm_num
    · -- Check (7 * 449 - 15) % 23 = 0
      norm_num
  · -- Show there is no smaller element in the set
    intro y hy
    rcases hy with ⟨hy1, hy2, hy3⟩
    rw [Finset.mem_Icc] at hy1
    rcases hy1 with ⟨hy1l, hy1r⟩
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num at hy2 hy3 <;> all_goals
      omega