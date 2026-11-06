import Mathlib

theorem number_theory_7842 : ¬∃ (x y : ℤ), x^2 = y^5 - 4 := by 
  rintro ⟨x, y, h_eq⟩

  have h_mod_eq : x^2 % 11 = 0 ∨ x^2 % 11 = 1 ∨ x^2 % 11 = 3 ∨ x^2 % 11 = 4 ∨ x^2 % 11 = 5 ∨ x^2 % 11 = 9 := by
    have h1 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1] at *
  
  have h_mod_eq' : (x^2) % 11 = 6 ∨ (x^2) % 11 = 7 ∨ (x^2) % 11 = 8 := by 
    have h1 : y^5 % 11 = 0 ∨ y^5 % 11 = 1 ∨ y^5 % 11 = 10 := by
      have h2 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by 
        omega 
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at *
 
    have h2 : x^2 = y^5 - 4 := by linarith [h_eq]

    omega
  
  omega