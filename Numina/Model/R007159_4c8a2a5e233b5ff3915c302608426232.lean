import Mathlib

theorem number_theory_14863 :
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ 55 * n ≡ 165 [MOD 260]} 991 := by
  constructor
  · -- Show that 991 is in the set
    constructor
    · -- Show 991 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Verify 55 * 991 ≡ 165 [MOD 260]
      native_decide
  · -- Show that for all n in the set, n ≤ 991
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    norm_num [Nat.ModEq] at hn2
    by_contra h
    push_neg at h
    interval_cases n <;> omega