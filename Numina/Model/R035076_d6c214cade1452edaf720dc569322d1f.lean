import Mathlib

theorem number_theory_57227 (a b c d : ℤ) : 12 ∣ (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) := by 
  have h1 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 4 = 0 := by
    have h2 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
      omega 
    have h3 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
      omega
    have h4 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by 
      omega
    have h5 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5) <;> simp [Int.mul_emod, Int.sub_emod, h2, h3, h4, h5]

  have h2 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 3 = 0 := by 
    have h6 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
      omega 
    have h7 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by 
      omega 
    have h8 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by 
      omega 
    have h9 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by 
      omega 
    rcases h6 with (h6 | h6 | h6) <;> rcases h7 with (h7 | h7 | h7) <;> rcases h8 with (h8 | h8 | h8) <;> rcases h9 with (h9 | h9 | h9) <;> simp [Int.mul_emod, Int.sub_emod, h6, h7, h8, h9]

  omega