import Mathlib

theorem number_theory_48803 : ¬∃ (x y : ℤ), x^2 + y^2 = 1979 := by
  rintro ⟨x, y, h⟩
  have h1 : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
    have h2 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2) <;> 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h2] at *
  have h2 : y^2 % 4 = 0 ∨ y^2 % 4 = 1 := by 
    have h3 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3) <;> 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h3] at *
  have h3 : (x^2 + y^2) % 4 = 0 ∨ (x^2 + y^2) % 4 = 1 ∨ (x^2 + y^2) % 4 = 2 := by 
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> 
      omega 
  have h4 : (1979 : ℤ) % 4 = 3 := by 
    norm_num 
  omega