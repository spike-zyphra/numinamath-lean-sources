import Mathlib

theorem number_theory_191633 {a b c : ℤ} (h : 6 ∣ a + b + c) :
    6 ∣ a^3 + b^3 + c^3 := by
  have h1 : a % 6 = 0 ∨ a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by
    omega
  have h2 : b % 6 = 0 ∨ b % 6 = 1 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4 ∨ b % 6 = 5 := by
    omega
  have h3 : c % 6 = 0 ∨ c % 6 = 1 ∨ c % 6 = 2 ∨ c % 6 = 3 ∨ c % 6 = 4 ∨ c % 6 = 5 := by
    omega

  have h4 : a^3 % 6 = a % 6 := by
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> 
      norm_num [h1, pow_succ, Int.add_emod, Int.mul_emod]

  have h5 : b^3 % 6 = b % 6 := by
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> 
      norm_num [h2, pow_succ, Int.add_emod, Int.mul_emod]

  have h6 : c^3 % 6 = c % 6 := by
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> 
      norm_num [h3, pow_succ, Int.add_emod, Int.mul_emod]

  have h7 : (a + b + c) % 6 = 0 := by 
    omega

  have h8 : (a^3 + b^3 + c^3) % 6 = 0 := by 
    omega

  exact Int.dvd_of_emod_eq_zero h8