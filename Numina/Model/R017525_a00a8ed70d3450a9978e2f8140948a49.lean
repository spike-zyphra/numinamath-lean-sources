import Mathlib

theorem number_theory_210260 : ¬∃ x y : ℤ, x^2 = y^5 - 4 := by
  rintro ⟨x, y, h⟩
  have h1 : x^2 % 11 = 0 ∨ x^2 % 11 = 1 ∨ x^2 % 11 = 3 ∨ x^2 % 11 = 4 ∨ x^2 % 11 = 5 ∨ x^2 % 11 = 9 := by
    have h2 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_two, Int.add_emod, Int.mul_emod]
  have h2 : y^5 % 11 = 0 ∨ y^5 % 11 = 1 ∨ y^5 % 11 = 10 := by
    have h3 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
  -- Compute both sides of the equation modulo 11
  have h3 : (x ^ 2) % 11 = (y ^ 5 - 4) % 11 := by 
    omega
  omega