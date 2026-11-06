import Mathlib

theorem number_theory_19436 :
    IsLeast {n | 1 < n ∧ ∃ x, n * x ≡ 1 [MOD 130] ∧ ∃ y, n * y ≡ 1 [MOD 231]} 17 := by
  constructor
  · -- First, we verify that 17 is in the set
    constructor
    · norm_num
    · -- Show existence of x and y such that the congruences hold
      use 23
      constructor
      · -- Show 17 * 23 ≡ 1 [MOD 130]
        norm_num [Nat.ModEq]
      · -- Show existence of y
        use 68
        all_goals -- Show 17 * 68 ≡ 1 [MOD 231]
          norm_num [Nat.ModEq]
  · -- Now, we verify that 17 is the smallest element
    intro n hn
    rcases hn with ⟨hn1, x, h1, y, h2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { 
      simp [Nat.ModEq] at h1 h2 
      all_goals 
        try { 
          omega 
        } 
        <;> try { 
          norm_num at h1 h2 
          all_goals 
            try { 
              omega 
            }
            <;> try { 
              exfalso 
              <;> try { 
                tauto 
              } 
              <;> try { 
                omega 
              }
            }
        }
    }