import Mathlib

theorem number_theory_182217 : IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ (n + 184952) % 2 = 0 ∧ (n + 184952) % 3 = 0 ∧ (n + 184952) % 7 = 0} 982 := by
  constructor
  · -- Show 982 is in the set
    constructor
    · -- Show 982 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that (982 + 184952) % 2 = 0
      norm_num
    constructor
    · -- Show that (982 + 184952) % 3 = 0
      norm_num
    · -- Show that (982 + 184952) % 7 = 0
      norm_num
  · -- Show that 982 is the greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h100, h999⟩
    by_contra h
    push_neg at h
    interval_cases n <;> omega