import Mathlib

theorem number_theory_252124 (x y z : ℕ) (h₀ : 7 ∣ x^3 + y^3 + z^3) : 7 ∣ x * y * z := by
  have h1 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
    omega

  have h2 : y % 7 = 0 ∨ y % 7 = 1 ∨ y % 7 = 2 ∨ y % 7 = 3 ∨ y % 7 = 4 ∨ y % 7 = 5 ∨ y % 7 = 6 := by
    omega

  have h3 : z % 7 = 0 ∨ z % 7 = 1 ∨ z % 7 = 2 ∨ z % 7 = 3 ∨ z % 7 = 4 ∨ z % 7 = 5 ∨ z % 7 = 6 := by
    omega

  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> ( 
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, pow_succ, h1, h2, h3, Nat.pow_mod] at h₀ ⊢
    <;> omega 
  )