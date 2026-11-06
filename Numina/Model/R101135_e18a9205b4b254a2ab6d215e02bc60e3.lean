import Mathlib

theorem number_theory_124968 :
    ∀ n : ℕ, ∃ m > n, ¬∃ x y z : ℤ, x^4 + y^4 + z^4 = m := by 
  intro n
  use 16 * n + 4
  constructor
  · -- Show m > n
    omega
  · -- Show ¬∃ x y z : ℤ, x^4 + y^4 + z^4 = m
    rintro ⟨x, y, z, h⟩
    have h1 : x^4 % 16 = 0 ∨ x^4 % 16 = 1 := by
      have h1 : x % 16 = 0 ∨ x % 16 = 1 ∨ x % 16 = 2 ∨ x % 16 = 3 ∨ x % 16 = 4 ∨ x % 16 = 5 ∨ x % 16 = 6 ∨ x % 16 = 7 ∨ x % 16 = 8 ∨ x % 16 = 9 ∨ x % 16 = 10 ∨ x % 16 = 11 ∨ x % 16 = 12 ∨ x % 16 = 13 ∨ x % 16 = 14 ∨ x % 16 = 15 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
    have h2 : y^4 % 16 = 0 ∨ y^4 % 16 = 1 := by
      have h1 : y % 16 = 0 ∨ y % 16 = 1 ∨ y % 16 = 2 ∨ y % 16 = 3 ∨ y % 16 = 4 ∨ y % 16 = 5 ∨ y % 16 = 6 ∨ y % 16 = 7 ∨ y % 16 = 8 ∨ y % 16 = 9 ∨ y % 16 = 10 ∨ y % 16 = 11 ∨ y % 16 = 12 ∨ y % 16 = 13 ∨ y % 16 = 14 ∨ y % 16 = 15 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
    have h3 : z^4 % 16 = 0 ∨ z^4 % 16 = 1 := by
      have h1 : z % 16 = 0 ∨ z % 16 = 1 ∨ z % 16 = 2 ∨ z % 16 = 3 ∨ z % 16 = 4 ∨ z % 16 = 5 ∨ z % 16 = 6 ∨ z % 16 = 7 ∨ z % 16 = 8 ∨ z % 16 = 9 ∨ z % 16 = 10 ∨ z % 16 = 11 ∨ z % 16 = 12 ∨ z % 16 = 13 ∨ z % 16 = 14 ∨ z % 16 = 15 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h] at *
    omega