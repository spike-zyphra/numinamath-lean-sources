import Mathlib

theorem number_theory_182905 :
    ∀ n : ℕ, ∃ m : ℕ, m > n ∧ ¬∃ x y z : ℤ, m = x^3 + y^3 + z^3 := by
  intro n
  use 9 * n + 4
  constructor
  · -- Show that m > n
    omega
  · -- Show that there do not exist integers x, y, z such that m = x^3 + y^3 + z^3
    intro h
    rcases h with ⟨x, y, z, h_eq⟩
    have h1 : (x ^ 3 + y ^ 3 + z ^ 3 : ℤ) % 9 = 4 := by
      omega
    have h2 : x^3 % 9 = 0 ∨ x^3 % 9 = 1 ∨ x^3 % 9 = 8 := by
      have h1 : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by 
        omega
      rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod] 
    have h3 : y^3 % 9 = 0 ∨ y^3 % 9 = 1 ∨ y^3 % 9 = 8 := by
      have h1 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by 
        omega
      rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    have h4 : z^3 % 9 = 0 ∨ z^3 % 9 = 1 ∨ z^3 % 9 = 8 := by
      have h1 : z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8 := by 
        omega
      rcases h1 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega -- This should derive a contradiction