import Mathlib

theorem number_theory_23155 :
    IsLeast {n | n ∈ Finset.Icc 10000 99999 ∧ 
                 (Nat.digits 10 n).toFinset.card = 5 ∧ 
                 (∀d ∈ Nat.digits 10 n, d ≠ 0 → d ∣ n)} 10236 := by 
  constructor
  · -- Verify 10236 is in the set
    constructor
    · -- Show it's in the range [10000, 99999]
      exact Finset.mem_Icc.mpr (by norm_num)
    constructor
    · -- Show all digits are distinct
      native_decide
    · -- Show divisible by each non-zero digit
      native_decide
  · -- Show 10236 is the smallest
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn11, hn12⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn2 hn3 ⊢
    <;> try { contradiction }
    <;> omega