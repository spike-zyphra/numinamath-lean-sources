import Mathlib
theorem number_theory_610784 : IsLeast {n : ℕ | n > 72 ∧ Nat.primeFactors n = Nat.primeFactors 72} 96:= by
  constructor
  · -- Verify 96 is in the set.
    constructor
    · -- Verify 96 > 72.
      norm_num
    · -- Verify Nat.primeFactors 96 = Nat.primeFactors 72.
      native_decide
  · -- Verify there is no smaller element in the set.
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : n < 96 := by linarith
    interval_cases n <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at hn2 ⊢ <;> all_goals contradiction