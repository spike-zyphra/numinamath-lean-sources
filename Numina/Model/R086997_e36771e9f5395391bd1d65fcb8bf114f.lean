import Mathlib

theorem number_theory_11917 :
    IsLeast {n | 0 < n ∧ n.primeFactors.card = 3} 30 := by
  constructor
  · -- Verify 30 is in the set
    constructor
    · norm_num
    · -- Check that 30 has exactly 3 prime factors
      native_decide
  · -- Show that 30 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_primecount⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at hn_primecount <;> all_goals omega