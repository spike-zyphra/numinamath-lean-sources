import Mathlib

theorem number_theory_4905 :
    IsGreatest {x | x ∈ Finset.Icc 100 999 ∧ x ≡ 17 [MOD 21] ∧ Even x} 962 := by
  constructor
  · -- Show 962 is in the set
    refine ⟨by norm_num [Finset.mem_Icc], by norm_num [Nat.ModEq], by decide⟩
  · -- Show that any number in the set is ≤ 962
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    norm_num [Nat.ModEq, Nat.even_iff] at hn2 hn3
    by_contra h
    push_neg at h
    interval_cases n <;> omega