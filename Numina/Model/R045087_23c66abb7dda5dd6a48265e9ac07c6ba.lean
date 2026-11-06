import Mathlib

theorem number_theory_240695 : ∃ a d : ℤ, a > 0 ∧ d > 0 ∧ ∀ n : ℤ, n > 0 →
¬∃ m p : ℤ, m > 0 ∧ p > 0 ∧ (a + d * n = m ^ 2 + p ^ 2 ∨ a + d * n = m ^ 3 + p ^ 3) := by
  use 31
  use 36
  constructor
  · -- Show a > 0
    norm_num
  constructor
  · -- Show d > 0
    norm_num
  · -- Show that for all n > 0
    intro n hn
    rintro ⟨m, p, hm, hp, h | h⟩
    · -- Case 1: $31 + 36n = m^2 + p^2$.
      have h1 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by 
        have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h2 : p ^ 2 % 4 = 0 ∨ p ^ 2 % 4 = 1 := by 
        have h2 : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
        rcases h2 with (h2 | h2 | h2 | h2) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2]
      have h3 : (m ^ 2 + p ^ 2) % 4 = 3 := by
        omega
      omega 
    · -- Case 2: $31 + 36n = m^3 + p^3$.
      have h1 : m ^ 3 % 9 = 0 ∨ m ^ 3 % 9 = 1 ∨ m ^ 3 % 9 = 8 := by 
        have h1 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by omega
        rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
          simp [pow_succ, Int.add_emod, Int.mul_emod, h1]
      have h2 : p ^ 3 % 9 = 0 ∨ p ^ 3 % 9 = 1 ∨ p ^ 3 % 9 = 8 := by 
        have h2 : p % 9 = 0 ∨ p % 9 = 1 ∨ p % 9 = 2 ∨ p % 9 = 3 ∨ p % 9 = 4 ∨ p % 9 = 5 ∨ p % 9 = 6 ∨ p % 9 = 7 ∨ p % 9 = 8 := by omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
          simp [pow_succ, Int.add_emod, Int.mul_emod, h2]
      have h3 : (m ^ 3 + p ^ 3) % 9 = 4 := by 
        omega
      omega