import Mathlib

theorem number_theory_287864 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), n % d = 0} 9864 := by

  constructor
  · -- First, we need to prove that 9864 is in our set.
    constructor
    · -- Show 9864 is in the range [1000, 9999]
      simp [Finset.mem_Icc]
    constructor
    · -- Show that the length of digits of 9864 is 4
      native_decide
    constructor
    · -- Show that the cardinality of digit finset is 4 (all digits unique)
      native_decide
    · -- Show that 9864 is divisible by all its digits
      native_decide

  · -- We need to show that any number in the set is ≤ 9864
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4⟩

    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hl, hr⟩

    by_contra h
    push_neg at h
    -- n is in the range [9865, 9999]

    interval_cases n <;> norm_num at hn2 hn3 hn4 ⊢
    all_goals contradiction