import Mathlib

theorem number_theory_237331 :
    IsLeast {n | 2016 ∣ Nat.factorial n} 8 ∧
    IsLeast {n | 2016^10 ∣ Nat.factorial n} 63 := by
  constructor
  · -- Let's prove that 8 is the minimal natural number such that 2016 divides n!
    constructor
    · -- First, we check that 2016 indeed divides 8!
      native_decide
    · -- Now, we need to show that for all n such that 2016 divides n!, we have n ≥ 8
      intro n hn
      have h : 2016 ∣ Nat.factorial n := by
        simpa using hn
      by_contra h'
      push_neg at h'
      have : n < 8 := by omega
      interval_cases n <;> contradiction
      all_goals contradiction
  · -- Now, we work on the second part. Let's prove that 63 is the minimal natural number such that 2016^10 divides n!
    constructor
    · -- First, we check that 2016^10 indeed divides 63!
      native_decide
    · -- Now, we need to show that for all n such that 2016^10 divides n!, we have n ≥ 63
      intro n hn
      have h : 2016^10 ∣ Nat.factorial n := by
        simpa using hn
      by_contra h'
      push_neg at h'
      have : n < 63 := by omega
      interval_cases n <;> contradiction