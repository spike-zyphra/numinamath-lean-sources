import Mathlib

theorem number_theory_242350 (a b c : ℤ) : ¬(8 ∣ a^2 + b^2 + c^2 - 7) := by 
  intro h
  have h1 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
    have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> ( 
      norm_num [h1, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] 
    )
  have h2 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by 
    have h2 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
      norm_num [h2, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] 
    )
  have h3 : c^2 % 8 = 0 ∨ c^2 % 8 = 1 ∨ c^2 % 8 = 4 := by 
    have h3 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> ( 
      norm_num [h3, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] 
    )
  have h4 : (a^2 + b^2 + c^2) % 8 = 7 := by 
    omega 
  rcases h1 with (ha | ha | ha) <;> rcases h2 with (hb | hb | hb) <;> rcases h3 with (hc | hc | hc) <;> omega