import Mathlib

theorem number_theory_105661 :
    IsLeast {p : ℕ | 0 < p ∧ p.Prime ∧ ∃ n, p ∣ n ^ 2 + 5 * n + 23} 17 := by
  constructor
  · -- Show 17 is in the set
    constructor
    · norm_num 
    constructor
    · norm_num 
    · use 14
      all_goals
        norm_num
  · -- Show no smaller element is in the set
    intro p hp
    rcases hp with ⟨hp_pos, hp_prime, ⟨n, hn⟩⟩
    by_contra h
    push_neg at h
    have h1 : p < 17 := h
    interval_cases p <;> norm_num at hp_prime hp_pos hn ⊢ 
    all_goals 
      try { 
        omega
      }
      <;> try { 
          have h2 : (n ^ 2 + 5 * n + 23) % 2 = 1 := by
            have : n % 2 = 0 ∨ n % 2 = 1 := by omega
            rcases this with (h | h)
            all_goals simp [h, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
          omega 
        }
      <;> try { 
          have h2 : (n ^ 2 + 5 * n + 23) % 3 = 1 ∨ (n ^ 2 + 5 * n + 23) % 3 = 2 := by
            have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
            rcases h1 with (h1 | h1 | h1)
            all_goals simp [h1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
          omega 
        }
      <;> try { 
          have h2 : (n ^ 2 + 5 * n + 23) % 5 ≠ 0 := by
            have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at *
          omega 
        }
      <;> try { 
          have h2 : (n ^ 2 + 5 * n + 23) % 7 ≠ 0 := by
            have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at *
          omega 
        }
      <;> try { 
          have h2 : (n ^ 2 + 5 * n + 23) % 11 ≠ 0 := by 
            have h1 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at *
          omega 
        }
      <;> try { 
          have h2 : (n ^ 2 + 5 * n + 23) % 13 ≠ 0 := by
            have h1 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [h1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at *
          omega 
        }