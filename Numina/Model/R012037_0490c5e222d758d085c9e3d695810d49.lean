import Mathlib

theorem number_theory_168014 :
    IsLeast {m | 0 < m ∧ Nat.fib m ≡ 0 [MOD 127] ∧ Nat.fib (m + 1) ≡ 1 [MOD 127]} 256 := by
  constructor
  · -- Show 256 is in the set
    constructor
    · norm_num
    constructor
    · -- Verify that Nat.fib 256 ≡ 0 [MOD 127]
      native_decide
    · -- Verify that Nat.fib (256 + 1) ≡ 1 [MOD 127]
      native_decide
  · -- Show there is no smaller element in the set
    intro m hm
    rcases hm with ⟨hm_pos, hm1, hm2⟩
    by_contra h
    push_neg at h
    interval_cases m <;> norm_num [Nat.ModEq] at hm1 hm2 <;> try { contradiction }