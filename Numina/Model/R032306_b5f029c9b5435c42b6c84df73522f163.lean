import Mathlib
set_option maxRecDepth 1000

theorem algebra_12272 :
    IsLeast {n > 1 | ¬Nat.Prime n ∧ ∀ p, p.Prime → p < 10 → ¬p ∣ n} 121 := by
  constructor
  · -- We verify that 121 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    · intro p hp h
      have h2 : p < 10 := h
      have h3 : p ≤ 9 := by linarith
      by_contra h4
      have h4 : p ∣ 121 := by tauto
      interval_cases p <;> norm_num at hp h4 h <;> tauto
  · -- Now we need to prove that 121 is the least in the set.
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    by_contra h
    push_neg at h
    have h3 : n < 121 := h
    have h4 : n > 1 := hn1
    have h5 : ¬Nat.Prime n := hn2
    have h6 : ∀ p, p.Prime → p < 10 → ¬p ∣ n := hn3
    have h15 : ∃ p, p.Prime ∧ p ∣ n ∧ p < 10 := by
      by_cases h2 : n % 2 = 0
      · -- n is even, so 2 divides n
        use 2
        constructor
        · norm_num
        constructor
        · -- Show 2 divides n
          omega
        · norm_num
      by_cases h3 : n % 3 = 0
      · -- n is divisible by 3
        use 3
        constructor
        · norm_num
        constructor
        · -- Show 3 divides n
          omega
        · norm_num
      by_cases h5 : n % 5 = 0
      · -- n is divisible by 5
        use 5
        constructor
        · norm_num
        constructor
        · -- Show 5 divides n
          omega
        · norm_num
      by_cases h7 : n % 7 = 0
      · -- n is divisible by 7
        use 7
        constructor
        · norm_num
        constructor
        · -- Show 7 divides n
          omega
        · norm_num
      have h8 : n ≤ 120 := by linarith
      interval_cases n <;> norm_num at hn1 hn2 h2 h3 h5 h7 ⊢
      <;> try { tauto }
    rcases h15 with ⟨p, hp1, hp2, hp3⟩
    have hp4 : ¬p ∣ n := h6 p hp1 hp3
    contradiction