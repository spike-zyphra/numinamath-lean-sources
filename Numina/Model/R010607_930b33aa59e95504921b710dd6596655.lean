import Mathlib

theorem number_theory_69550 (m : ℕ) (hm : m > 0) : 42 ∣ m^7 - m := by 
  have h1 : m^7 % 2 = m % 2 := by
    have h1 : m % 2 = 0 ∨ m % 2 = 1 := by 
      omega 
    rcases h1 with (h | h)
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
  
  have h2 : m^7 % 3 = m % 3 := by 
    have h1 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
      omega
    rcases h1 with (h | h | h)
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]

  have h3 : m^7 % 7 = m % 7 := by
    have h1 : m % 7 = 0 ∨ m % 7 = 1 ∨ m % 7 = 2 ∨ m % 7 = 3 ∨ m % 7 = 4 ∨ m % 7 = 5 ∨ m % 7 = 6 := by
      omega 
    rcases h1 with (h | h | h | h | h | h | h)
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]
    · 
      simp [Nat.pow_mod, h]

  have h4 : (m^7 - m) % 2 = 0 := by 
    omega

  have h5 : (m^7 - m) % 3 = 0 := by 
    omega

  have h6 : (m^7 - m) % 7 = 0 := by 
    omega

  omega