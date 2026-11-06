import Mathlib

theorem number_theory_157931 : ¬∃ x y : ℤ, x^3 + y^3 = 2020 := by
  rintro ⟨x, y, h⟩
  have h1 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by 
    have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
  have h2 : y^3 % 9 = 0 ∨ y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by
    have h2 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
  omega