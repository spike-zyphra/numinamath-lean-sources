import Mathlib

theorem number_theory_15556 : IsLeast {n | 1 < n ∧ ∃m, m * n ≡ 1 [MOD 1050] } 11 := by
  constructor
  · -- Show that 11 is in the set
    constructor
    · -- 11 is greater than 1
      norm_num
    · -- There exists m such that m * 11 ≡ 1 [MOD 1050]
      use 191
      norm_num [Nat.ModEq]
  · -- Show that 11 is the least
    intro n hn 
    rcases hn with ⟨hn1, ⟨m, hm⟩⟩ 
    by_contra h 
    push_neg at h 
    interval_cases n <;> simp [Nat.ModEq] at hm <;> try { 
      all_goals omega 
    }