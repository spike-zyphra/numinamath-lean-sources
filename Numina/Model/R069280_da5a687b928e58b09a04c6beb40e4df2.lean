import Mathlib

def is_nineHeavy (n : ℕ) := n % 9 > 5

theorem number_theory_15124 :
    IsLeast {n | n ∈ Finset.Icc 100 999 ∧ is_nineHeavy n} 105 := by
  constructor
  · -- Show that 105 belongs to the set
    constructor
    · -- Show that 105 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that 105 is nine-heavy
      norm_num [is_nineHeavy]
  · -- Show that there is no smaller number in the set
    intro n hn
    rcases hn with ⟨hnFinset, hnHeavy⟩
    rw [Finset.mem_Icc] at hnFinset
    rcases hnFinset with ⟨h100, h999⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [is_nineHeavy] at hnHeavy
    all_goals omega