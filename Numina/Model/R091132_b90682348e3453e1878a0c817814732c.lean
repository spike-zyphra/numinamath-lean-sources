import Mathlib

theorem number_theory_319042 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) :
    3 ∣ a ∨ 3 ∣ b := by
  by_contra h
  push_neg at h
  have h1 : a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have h1' : b % 3 = 1 ∨ b % 3 = 2 := by 
    omega
  have h4 : a^2 % 3 = 1 := by 
    rcases h1 with (h1 | h1)
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1]
  have h5 : b^2 % 3 = 1 := by 
    rcases h1' with (h1' | h1')
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1']
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h1']
  have h6 : (a^2 + b^2) % 3 = 2 := by
    omega
  have h8 : c^2 % 3 = 0 ∨ c^2 % 3 = 1 := by
    have h9 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by 
      omega
    rcases h9 with (h9 | h9 | h9)
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h9]
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h9]
    · norm_num [pow_two, Int.add_emod, Int.mul_emod, h9]
  have h7 : c^2 % 3 = 2 := by 
    omega
  omega