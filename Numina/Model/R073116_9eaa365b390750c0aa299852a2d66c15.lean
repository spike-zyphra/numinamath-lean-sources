import Mathlib

theorem number_theory_158665 (a b c : ℕ) (h : a^2 + b^2 = c^2) :
    5 ∣ a ∨ 5 ∣ b ∨ 5 ∣ c := by 
  by_contra h1
  push_neg at h1

  have h2 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
    omega

  have h3 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
    omega

  have h4 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by 
    omega
  
  have h5 : (a ^ 2 : ℕ) % 5 = 1 ∨ (a ^ 2 : ℕ) % 5 = 4 := by 
    rcases h2 with (h2 | h2 | h2 | h2) <;> norm_num [Nat.pow_mod, h2]

  have h6 : (b ^ 2 : ℕ) % 5 = 1 ∨ (b ^ 2 : ℕ) % 5 = 4 := by 
    rcases h3 with (h3 | h3 | h3 | h3) <;> norm_num [Nat.pow_mod, h3]

  have h7 : (c ^ 2 : ℕ) % 5 = 1 ∨ (c ^ 2 : ℕ) % 5 = 4 := by 
    rcases h4 with (h4 | h4 | h4 | h4) <;> norm_num [Nat.pow_mod, h4]

  have h8 : ((a ^ 2 + b ^ 2) : ℕ) % 5 = (c ^ 2 : ℕ) % 5 := by
    omega

  omega