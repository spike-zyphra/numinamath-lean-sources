import Mathlib

theorem number_theory_207284 (m n : ℕ) :
    Nat.factorial m + 2 = n ^ 2 ↔ (m = 2 ∧ n = 2) := by
  constructor
  · -- Forward direction: if Nat.factorial m + 2 = n ^ 2 then (m = 2 ∧ n = 2)
    intro h
    by_cases h1 : m ≤ 3
    · -- Case 1: m ≤ 3
      interval_cases m <;> try { 
        simp [Nat.factorial] at h 
        all_goals 
          have h2 : n ≤ 3 := by nlinarith 
          interval_cases n <;> omega 
      }
    · -- Case 2: m > 3
      have h2 : m ≥ 4 := by 
        omega 
      have h3 : 4 ∣ Nat.factorial m := by 
        apply Nat.dvd_factorial 
        all_goals 
          omega 
      have h4 : (Nat.factorial m : ℕ) % 4 = 0 := by 
        have h5 : 4 ∣ Nat.factorial m := h3 
        omega 
      have h5 : (n ^ 2 : ℕ) % 4 = 2 := by 
        omega 
      have h6 : (n ^ 2 : ℕ) % 4 = 0 ∨ (n ^ 2 : ℕ) % 4 = 1 := by
        have h7 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega 
        rcases h7 with (h7 | h7 | h7 | h7) <;> simp [Nat.pow_mod, Nat.mul_mod, h7]
      omega 
  · -- Backward direction: if (m = 2 ∧ n = 2) then Nat.factorial m + 2 = n ^ 2
    rintro ⟨rfl, rfl⟩ 
    norm_num [Nat.factorial]