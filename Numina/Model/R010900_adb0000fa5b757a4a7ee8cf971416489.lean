import Mathlib

theorem number_theory_609646 :
    IsLeast {m | 0 < m ∧ Nat.fib m ≡ 0 [MOD 127] ∧ Nat.fib (m + 1) ≡ 1 [MOD 127]} 256 := by
  constructor
  · -- Show 256 is in the set
    constructor
    · norm_num
    constructor
    · -- Show that Nat.fib 256 ≡ 0 [MOD 127]
      native_decide
    · -- Show that Nat.fib 257 ≡ 1 [MOD 127]
      native_decide
  · -- Show there is no smaller element in the set
    intro m hm
    rcases hm with ⟨hm0, h1, h2⟩
    by_contra h
    push_neg at h
    interval_cases m <;> try { 
      simp [Nat.ModEq] at h1 h2
      all_goals 
      try { contradiction }
    } <;> try { native_decide }