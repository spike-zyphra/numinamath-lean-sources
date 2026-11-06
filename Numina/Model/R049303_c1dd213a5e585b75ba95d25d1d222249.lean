import Mathlib

theorem number_theory_5063 :
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ Even n ∧ n ≡ 14 [MOD 23]} 980 := by
  constructor
  · -- 980 is in the set
    constructor
    · -- Show that 980 is in the range [100, 999]
      simp [Finset.mem_Icc]
    constructor
    · -- Show that 980 is even
      exact ⟨490, by norm_num⟩
    · -- Show that 980 ≡ 14 [MOD 23]
      norm_num [Nat.ModEq]
  · -- Show that for any n in the set, n ≤ 980
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn4, hn5⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.ModEq] at hn3 <;> try { tauto }
    all_goals contradiction