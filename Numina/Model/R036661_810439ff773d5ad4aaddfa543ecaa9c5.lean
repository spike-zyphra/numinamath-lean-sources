import Mathlib

theorem number_theory_275796 (a b c : ℤ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) :
    Even a ∨ Even b ∨ Even c ∧ ¬(Odd a ∧ Odd b ∧ Odd c) := by
  by_cases h : Even a
  · -- If a is even, we satisfy the first part of the disjunction
    left
    exact h
  · -- Consider the case where a is not even (so a is odd)
    by_cases h' : Even b
    · -- If b is even, we satisfy the second part of the disjunction
      right
      left
      exact h'
    · -- If neither a nor b is even, both are odd
      have ha1 : Odd a := by 
        simpa using h
      have hb1 : Odd b := by 
        simpa using h'
      have h4 : (a : ℤ) ^ 2 % 8 = 1 := by
        have h5 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
          rcases ha1 with ⟨k, hk⟩
          omega
        rcases h5 with (h5 | h5 | h5 | h5) <;> 
          norm_num [h5, pow_two, Int.add_emod, Int.mul_emod] at *
      have h5 : (b : ℤ) ^ 2 % 8 = 1 := by
        have h6 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
          rcases hb1 with ⟨k, hk⟩
          omega
        rcases h6 with (h6 | h6 | h6 | h6) <;> 
          norm_num [h6, pow_two, Int.add_emod, Int.mul_emod] at *
      have h6 : (c : ℤ) ^ 2 % 8 = 0 ∨ (c : ℤ) ^ 2 % 8 = 1 ∨ (c : ℤ) ^ 2 % 8 = 4 := by
        have h7 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by omega
        rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7) <;> 
          norm_num [h7, pow_two, Int.add_emod, Int.mul_emod]
      have h7 : (a ^ 2 + b ^ 2) % 8 = 2 := by
        omega
      have h8 : (c ^ 2) % 8 = 2 := by 
        omega
      omega