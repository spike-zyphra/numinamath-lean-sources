import Mathlib

theorem number_theory_292497 : ¬ ∃ (x y : ℤ), x^2 + 1974 = y^2 := by
  rintro ⟨x, y, h⟩
  have h1 : y^2 % 4 = 0 ∨ y^2 % 4 = 1 := by
    have h2 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> 
      norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h2] at *
  
  have h2 : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by 
    have h3 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3) <;> 
      norm_num [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h3] at *
  
  have h3 : (y^2 - x^2) % 4 = 2 := by 
    omega
  
  have h4 : (y^2 - x^2) % 4 = -1 ∨ (y^2 - x^2) % 4 = 0 ∨ (y^2 - x^2) % 4 = 1 := by 
    rcases h1 with (h1 | h1)
    <;> rcases h2 with (h2 | h2)
      <;> omega
  
  omega