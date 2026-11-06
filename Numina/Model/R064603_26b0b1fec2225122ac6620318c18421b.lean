import Mathlib

theorem number_theory_116186 (a b c : ℤ) (h : 9 ∣ a^3 + b^3 + c^3) :
    3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c := by 
  by_contra h'
  have h1 : a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨ a % 9 = 7 ∨ a % 9 = 8 := by 
    omega
  have h2 : b % 9 = 1 ∨ b % 9 = 2 ∨ b % 9 = 4 ∨ b % 9 = 5 ∨ b % 9 = 7 ∨ b % 9 = 8 := by 
    omega
  have h3 : c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 7 ∨ c % 9 = 8 := by 
    omega
  have h4 : a^3 % 9 = 1 ∨ a^3 % 9 = 8 := by
    rcases h1 with (h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_emod, h] 
  have h5 : b^3 % 9 = 1 ∨ b^3 % 9 = 8 := by
    rcases h2 with (h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_emod, h] 
  have h6 : c^3 % 9 = 1 ∨ c^3 % 9 = 8 := by
    rcases h3 with (h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, Int.emod_emod, h] 
  have h7 : (a^3 + b^3 + c^3) % 9 = 0 := by 
    omega
  omega