import Mathlib

theorem number_theory_123669 : ¬∃ a b, 2022 = a^2 - b^2 := by
  rintro ⟨a, b, h_eq⟩
  have h1 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by
    have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
      norm_num [pow_two, Nat.mul_mod, h1] at *
  
  have h2 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by
    have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> 
      norm_num [pow_two, Nat.mul_mod, h2] at *
  
  omega