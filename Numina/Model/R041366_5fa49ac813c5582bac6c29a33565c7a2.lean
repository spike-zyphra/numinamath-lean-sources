import Mathlib

theorem number_theory_8482 (x y : ℤ) : y ^ 2 = x ^ 5 - 4 ↔ False := by 
  constructor
  · -- Assume $y^2 = x^5 - 4$, prove False
    intro h_eq
    have h1 : y ^ 2 + 4 = x ^ 5 := by 
      nlinarith 
    have h2 : y ^ 2 % 11 = 0 ∨ y ^ 2 % 11 = 1 ∨ y ^ 2 % 11 = 3 ∨ y ^ 2 % 11 = 4 ∨ y ^ 2 % 11 = 5 ∨ y ^ 2 % 11 = 9 := by
      have h4 : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨ y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
        simp [h4, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h3 : x ^ 5 % 11 = 0 ∨ x ^ 5 % 11 = 1 ∨ x ^ 5 % 11 = 10 := by
      have h4 : x % 11 = 0 ∨ x % 11 = 1 ∨ x % 11 = 2 ∨ x % 11 = 3 ∨ x % 11 = 4 ∨ x % 11 = 5 ∨ x % 11 = 6 ∨ x % 11 = 7 ∨ x % 11 = 8 ∨ x % 11 = 9 ∨ x % 11 = 10 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> 
        simp [h4, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h4 : (y ^ 2 + 4) % 11 = x ^ 5 % 11 := by
      omega
    omega 
  · -- False implies anything
    intro h
    cases h