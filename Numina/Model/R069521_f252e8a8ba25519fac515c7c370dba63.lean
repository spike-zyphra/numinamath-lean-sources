import Mathlib

theorem number_theory_114940 : ¬∃ x y z : ℤ, x^3 + y^3 = 9 * z + 5 := by 
  rintro ⟨x, y, z, h_eq⟩
  have h1 : (x^3 + y^3) % 9 = (9 * z + 5) % 9 := by 
    omega
  have h2 : (9 * z + 5) % 9 = 5 := by 
    omega
  rw [h2] at h1
  have h3 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by
    have h4 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
      omega
    rcases h4 with (h | h | h | h | h | h | h | h | h) <;> 
      norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
  have h4 : y^3 % 9 = 0 ∨ y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by
    have h5 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
      omega
    rcases h5 with (h | h | h | h | h | h | h | h | h) <;> 
      norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
  have h5 : (x^3 + y^3) % 9 = 0 ∨ (x^3 + y^3) % 9 = 1 ∨ (x^3 + y^3) % 9 = 2 ∨ (x^3 + y^3) % 9 = 7 ∨ (x^3 + y^3) % 9 = 8 := by 
    rcases h3 with (h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4) <;> 
      omega
  omega