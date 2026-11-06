import Mathlib

theorem number_theory_240939 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a^2 + b^2 = c^2) :
    Even a ∨ Even b ∨ Even c := by
  by_contra h1
  push_neg at h1

  have h2 : ¬Even a := by 
    tauto
  have h3 : ¬Even b := by
    tauto
  have h4 : ¬Even c := by
    tauto
  
  have h5 : Odd a := by 
    simpa using h2
  have h6 : Odd b := by
    simpa using h3
  have h7 : Odd c := by
    simpa using h4
  
  have h8 : a % 2 = 1 := by
    rcases h5 with ⟨k, hk⟩
    omega

  have h9 : b % 2 = 1 := by
    rcases h6 with ⟨k, hk⟩
    omega

  have h10 : c % 2 = 1 := by
    rcases h7 with ⟨k, hk⟩
    omega
  
  have h11 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
    omega

  have h12 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
    omega

  have h13 : c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by 
    omega
  
  have h14 : a^2 % 8 = 1 := by 
    rcases h11 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]

  have h15 : b^2 % 8 = 1 := by 
    rcases h12 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]

  have h16 : c^2 % 8 = 1 := by 
    rcases h13 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]

  omega