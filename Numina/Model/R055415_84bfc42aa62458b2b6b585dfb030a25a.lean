import Mathlib

theorem number_theory_177558 (a b c : ℤ) :
    a^2 + b^2 - 8 * c = 6 ↔ False := by 
  constructor
  · -- Assume a^2 + b^2 - 8 * c = 6, prove False
    intro h
    have h1 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
      have h2 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
        norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] 
    have h2 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by 
      have h3 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
        omega 
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
        norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h3] 
    have h3 : (a^2 + b^2) % 8 = 6 := by 
      omega 
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> 
      omega 
  · -- Assume False, prove a^2 + b^2 - 8 * c = 6
    intro h
    exfalso
    exact h