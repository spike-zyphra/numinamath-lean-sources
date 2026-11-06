import Mathlib

theorem number_theory_229908 : ¬∃ x y z : ℤ, x^3 + y^6 = 7 * z + 3 := by
  rintro ⟨x, y, z, h_eq⟩
  have h1 : x ^ 3 % 7 = 0 ∨ x ^ 3 % 7 = 1 ∨ x ^ 3 % 7 = 6 := by
    have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
  have h2 : y ^ 6 % 7 = 0 ∨ y ^ 6 % 7 = 1 := by
    have h1 : y % 7 = 0 ∨ y % 7 = 1 ∨ y % 7 = 2 ∨ y % 7 = 3 ∨ y % 7 = 4 ∨ y % 7 = 5 ∨ y % 7 = 6 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
  have h3 : (x ^ 3 + y ^ 6) % 7 = 3 := by
    omega 
  omega