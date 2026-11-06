import Mathlib

theorem number_theory_287864 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), n % d = 0} 9864 := by
  constructor
  · -- First, let's verify 9864 satisfies our conditions:
    constructor
    · -- Check that 9864 belongs to the range [1000, 9999]
      native_decide
    constructor
    · -- Check that 9864 has 4 digits
      native_decide
    constructor
    · -- Check that 9864 has distinct digits
      native_decide
    · -- Check that 9864 is divisible by each of its digits
      native_decide
  · -- Now, let's show that 9864 is the largest such number
    intro n hn
    have ⟨hn1, hn2, hn3, hn4⟩ := hn
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> simp [Nat.digits, Nat.digitsAux] at hn2 hn3 hn4