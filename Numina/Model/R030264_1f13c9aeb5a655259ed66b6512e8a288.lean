import Mathlib

theorem number_theory_183993 (m n : ℕ) : 30 ∣ m * n * (m^4 - n^4) := by 
  have h1 : m * n * (m^4 - n^4) % 2 = 0 := by 
    have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega 
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega 
    rcases h1 with (h1 | h1)
    · -- m is even 
      have h3 : m * n % 2 = 0 := by 
        simp [Nat.mul_mod, h1] 
      have h4 : (m * n * (m^4 - n^4)) % 2 = 0 := by 
        simp [Nat.mul_mod, h3] 
      omega 
    · -- m is odd 
      rcases h2 with (h2 | h2)
      · -- n is even 
        have h3 : m * n % 2 = 0 := by 
          simp [Nat.mul_mod, h2] 
        have h4 : (m * n * (m^4 - n^4)) % 2 = 0 := by 
          simp [Nat.mul_mod, h3] 
        omega 
      · -- n is odd 
        have h3 : m % 2 = 1 := h1 
        have h4 : n % 2 = 1 := h2 
        have h5 : m^4 % 2 = 1 := by 
          have h1' : m % 2 = 1 := h3 
          have : m % 2 = 1 := h1' 
          have h2 : m^4 % 2 = 1 := by 
            simp [Nat.pow_mod, this] 
          omega 
        have h6 : n^4 % 2 = 1 := by 
          have h1' : n % 2 = 1 := h4 
          have : n % 2 = 1 := h1' 
          have h2 : n^4 % 2 = 1 := by 
            simp [Nat.pow_mod, this] 
          omega 
        have h7 : (m^4 - n^4) % 2 = 0 := by 
          omega 
        have h8 : (m * n * (m^4 - n^4)) % 2 = 0 := by 
          simp [Nat.mul_mod, h7] 
        omega 
  have h2 : m * n * (m^4 - n^4) % 3 = 0 := by 
    have h1 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega 
    have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega 
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) 
      <;> simp [Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, pow_succ, Nat.add_mod, h1, h2] 
      <;> omega 
  have h3 : m * n * (m^4 - n^4) % 5 = 0 := by 
    have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega 
    have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2) 
      <;> simp [Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, pow_succ, Nat.add_mod, h1, h2] 
      <;> omega 
  omega