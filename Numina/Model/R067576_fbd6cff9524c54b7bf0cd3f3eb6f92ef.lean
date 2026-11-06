import Mathlib

theorem number_theory_47049 (a b : ℤ) :
  (a^2 + b^2) % 4 ≠ 3 := by

  have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have h2 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  
  have ha2 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by
    rcases h1 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] <;> omega
  
  have hb2 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by
    rcases h2 with (h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h] <;> omega
  
  have h3 : (a^2 + b^2) % 4 = 0 ∨ (a^2 + b^2) % 4 = 1 ∨ (a^2 + b^2) % 4 = 2 := by 
    rcases ha2 with (h | h) <;> rcases hb2 with (h' | h') 
      <;> omega
  
  omega