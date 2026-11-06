import Mathlib

theorem number_theory_291207 :
    IsLeast {p : ℕ | ∃ n, p.Prime ∧ p ∣ n^2 + n + 11} 11 := by 
  constructor
  · -- Show 11 is in the set.
    use 0
    constructor
    · -- 11 is prime
      norm_num
    · -- Show 11 divides 0^2 + 0 + 11
      all_goals norm_num
  · -- Show 11 is the least
    intro p hp
    rcases hp with ⟨n, hp_prime, hp_div⟩
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp_prime hp_div <;> 
      try { 
        have : n ≤ 10 := by 
          by_contra h1
          push_neg at h1
          have h2 : (n ^ 2 + n + 11) % 2 = 1 := by
            have h1 : n % 2 = 0 ∨ n % 2 = 1 := by
              omega
            rcases h1 with (h1 | h1)
            · 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
            · 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
          omega
        interval_cases n <;> omega 
      }
      <;> try { 
        have : n ≤ 10 := by 
          by_contra h1 
          push_neg at h1
          have h2 : (n ^ 2 + n + 11) % 3 = 1 ∨ (n ^ 2 + n + 11) % 3 = 2 := by
            have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
              omega
            rcases h1 with (h1 | h1 | h1)
            · 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
            · 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
            · 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
          omega 
        interval_cases n <;> omega 
      }
      <;> try { 
        have : n ≤ 10 := by 
          by_contra h1
          push_neg at h1
          have h2 : (n ^ 2 + n + 11) % 5 = 1 ∨ (n ^ 2 + n + 11) % 5 = 2 ∨ (n ^ 2 + n + 11) % 5 = 3 ∨ (n ^ 2 + n + 11) % 5 = 4 := by
            have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
              omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1)
            all_goals 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
          omega 
        interval_cases n <;> omega 
      }
      <;> try { 
        have : n ≤ 10 := by 
          by_contra h1
          push_neg at h1
          have h2 : (n ^ 2 + n + 11) % 7 = 1 ∨ (n ^ 2 + n + 11) % 7 = 2 ∨ (n ^ 2 + n + 11) % 7 = 3 ∨ (n ^ 2 + n + 11) % 7 = 4 ∨ (n ^ 2 + n + 11) % 7 = 5 ∨ (n ^ 2 + n + 11) % 7 = 6 := by
            have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
              omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1)
            all_goals 
              simp [pow_two, Nat.add_mod, Nat.mul_mod, h1]
          omega 
        interval_cases n <;> omega 
      }