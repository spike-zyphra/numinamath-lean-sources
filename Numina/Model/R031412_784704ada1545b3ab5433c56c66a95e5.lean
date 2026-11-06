import Mathlib

theorem number_theory_99758 : ¬∃ x y, 19^19 = x^3 + y^4 := by
  rintro ⟨x, y, h⟩
  have h1 : x^3 + y^4 = 19^19 := by
    nlinarith
  have h4 : (x^3 + y^4) % 13 = 7 := by
    omega
  have h2 : x^3 % 13 = 0 ∨ x^3 % 13 = 1 ∨ x^3 % 13 = 5 ∨ x^3 % 13 = 8 ∨ x^3 % 13 = 12 := by 
    have h11 : x % 13 = 0 ∨ x % 13 = 1 ∨ x % 13 = 2 ∨ x % 13 = 3 ∨ x % 13 = 4 ∨ x % 13 = 5 ∨ x % 13 = 6 ∨ x % 13 = 7 ∨ x % 13 = 8 ∨ x % 13 = 9 ∨ x % 13 = 10 ∨ x % 13 = 11 ∨ x % 13 = 12 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [h, pow_succ, Nat.mul_mod, Nat.add_mod]
  have h3 : y^4 % 13 = 0 ∨ y^4 % 13 = 1 ∨ y^4 % 13 = 3 ∨ y^4 % 13 = 9 := by 
    have h11 : y % 13 = 0 ∨ y % 13 = 1 ∨ y % 13 = 2 ∨ y % 13 = 3 ∨ y % 13 = 4 ∨ y % 13 = 5 ∨ y % 13 = 6 ∨ y % 13 = 7 ∨ y % 13 = 8 ∨ y % 13 = 9 ∨ y % 13 = 10 ∨ y % 13 = 11 ∨ y % 13 = 12 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [h, pow_succ, Nat.mul_mod, Nat.add_mod]
  omega