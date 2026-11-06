import Mathlib

theorem number_theory_322987 : ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ x ^ 2 - 2 * y ^ 2 = 5 := by
  rintro ⟨x, y, hx, hy, heq⟩
  have h1 : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    have h1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.mul_mod, h1]
  have h2 : (2 * y ^ 2) % 8 = 0 ∨ (2 * y ^ 2) % 8 = 2 := by
    have h1 : y ^ 2 % 8 = 0 ∨ y ^ 2 % 8 = 1 ∨ y ^ 2 % 8 = 4 := by
      have h1 : y % 8 = 0 ∨ y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Nat.mul_mod, h1] at *
    omega
  have eq1 : x ^ 2 = 2 * y ^ 2 + 5 := by
    omega
  have h5 : x ^ 2 % 8 = 5 ∨ x ^ 2 % 8 = 7 := by
    omega
  omega