import Mathlib

theorem number_theory_605706 (m n : ℕ) : Nat.factorial n ≠ m^2 + 2019 := by
  by_contra h
  by_cases h1 : n < 9
  · -- When n < 9, we can check all the cases.
    interval_cases n <;> try { 
      simp [Nat.factorial] at h 
      all_goals 
      try { 
        have h2 : m ≤ 202 := by nlinarith 
        interval_cases m <;> omega 
      } 
    }
  · -- Assume n ≥ 9
    have h2 : n ≥ 9 := by 
      omega 
    -- Show 9 divides n!
    have h3 : 9 ∣ Nat.factorial n := by
      apply Nat.dvd_factorial 
      all_goals 
        omega 
    -- Show 9 divides m^2 + 2019
    have h4 : m^2 + 2019 = Nat.factorial n := by 
      linarith [h] 
    have h7 : (9) ∣ m^2 + 2019 := by 
      omega 
    -- Compute the value of (m^2) % 9
    have h8 : (m ^ 2) % 9 = 0 ∨ (m ^ 2) % 9 = 1 ∨ (m ^ 2) % 9 = 4 ∨ (m ^ 2) % 9 = 7 := by 
      have h9 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
        omega 
      rcases h9 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, Nat.mul_mod, h, Nat.add_mod, Nat.mul_mod]
    -- Contradicts with h7
    have h9 : (m ^ 2 + 2019) % 9 = 6 := by 
      omega 
    omega