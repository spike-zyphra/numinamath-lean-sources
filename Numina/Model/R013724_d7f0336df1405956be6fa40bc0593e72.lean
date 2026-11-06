import Mathlib

theorem number_theory_61982 (x y : ℤ) : x^2 + 4 ≠ y^5 := by 
  rintro h
  have h1 : x^2 + 4 = y^5 := by
    omega
  have h2 : x^2 % 11 = 0 ∨ x^2 % 11 = 1 ∨ x^2 % 11 = 3 ∨ x^2 % 11 = 4 ∨ x^2 % 11 = 5 ∨ x^2 % 11 = 9 := by
    have h11 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  have h3 : y^5 % 11 = 0 ∨ y^5 % 11 = 1 ∨ y^5 % 11 = 10 := by
    have h11 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by
      omega
    rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  have h4 : (x^2 + 4) % 11 = y^5 % 11 := by
    omega
  omega