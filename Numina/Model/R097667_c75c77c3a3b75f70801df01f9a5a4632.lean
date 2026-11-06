import Mathlib

theorem number_theory_6596 :
    ¬∃ x y z : ℤ, x^2 + y^2 + z^2 = 15 := by
  rintro ⟨x, y, z, h_eq⟩
  have h1 : x^2 % 8 = 0 ∨ x^2 % 8 = 1 ∨ x^2 % 8 = 4 := by 
    have h2 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h2]
  have h2 : y^2 % 8 = 0 ∨ y^2 % 8 = 1 ∨ y^2 % 8 = 4 := by 
    have h3 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h3]
  have h3 : z^2 % 8 = 0 ∨ z^2 % 8 = 1 ∨ z^2 % 8 = 4 := by 
    have h4 : z % 8 = 0 ∨ z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h4]
  have h4 : (x^2 + y^2 + z^2) % 8 = 7 := by
    omega
  omega