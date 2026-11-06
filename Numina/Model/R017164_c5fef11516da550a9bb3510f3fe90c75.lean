import Mathlib

theorem number_theory_85855 :
    ∀ n : ℕ, ∃ m : ℕ, m > n ∧ ¬∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ m = x^2 + y^2 + z^2 := by
  intro n
  use 8 * n + 7
  constructor
  · -- Show m > n
    omega
  · -- Assume there exist positive natural numbers x, y, z such that 8 * n + 7 = x^2 + y^2 + z^2
    intro h
    rcases h with ⟨x, y, z, hx, hy, hz, h_eq⟩
    have h1 : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
      have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    have h2 : y ^ 2 % 8 = 0 ∨ y ^ 2 % 8 = 1 ∨ y ^ 2 % 8 = 4 := by
      have h1 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    have h3 : z ^ 2 % 8 = 0 ∨ z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4 := by
      have h1 : z % 8 = 0 ∨ z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by
        omega
      rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    omega