import Mathlib

theorem number_theory_182079 : ¬∃ x y : ℕ, (2 * x + y) * (2 * y + x) = 2017 ^ 2017 := by 
  rintro ⟨x, y, h⟩
  have h1 : (2 * x + y) * (2 * y + x) % 3 = 1 := by
    omega
  have h2 : (2 * x + y) * (2 * y + x) % 3 = 0 ∨ (2 * x + y) * (2 * y + x) % 3 = 2 := by
    have h3 : (2 * x + y) * (2 * y + x) % 3 = 0 ∨ (2 * x + y) * (2 * y + x) % 3 = 2 := by
      have h1 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
        omega
      have h2 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
        omega
      rcases h1 with (h1 | h1 | h1)
      <;> rcases h2 with (h2 | h2 | h2)
      <;> simp [Nat.mul_mod, Nat.add_mod, h1, h2]
    exact h3
  omega