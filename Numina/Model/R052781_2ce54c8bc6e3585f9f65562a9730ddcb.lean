import Mathlib

theorem number_theory_3869 : IsLeast {n | (Nat.digits 10 n).length = 2 ∧ n^3 ≡ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)) [MOD 100]} 99 := by
  constructor
  · -- Prove 99 is in the set
    constructor
    · -- Check that 99 is two-digit
      native_decide
    · -- Check that 99^3 ≡ reverse(99) [MOD 100]
      native_decide
  · -- Now prove that 99 is the smallest such
    intro n hn
    rcases hn with ⟨h_length, h_mod⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h_length h_mod <;> all_goals contradiction