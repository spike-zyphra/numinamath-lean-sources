import Mathlib

theorem number_theory_6864 (x y : ℕ) : ¬(2*x)^4-y^2=2024 := by
  rintro h
  have h1 : (2 * x) ^ 4 = y ^ 2 + 2024 := by
    omega
  have h2 : (2 * x) ^ 4 % 16 = 0 := by
    have h3 : ∀ x : ℕ, (2 * x) ^ 4 % 16 = 0 := by
      intro x
      ring_nf
      <;> omega
    specialize h3 x
    simpa using h3
  have h3 : (y ^ 2 + 2024) % 16 = (y ^ 2 % 16 + 8) % 16 := by
    omega
  have h4 : (y ^ 2 % 16 + 8) % 16 = 0 := by 
    omega
  have h5 : y ^ 2 % 16 = 0 ∨ y ^ 2 % 16 = 1 ∨ y ^ 2 % 16 = 4 ∨ y ^ 2 % 16 = 9 := by
    have h : y % 16 = 0 ∨ y % 16 = 1 ∨ y % 16 = 2 ∨ y % 16 = 3 ∨ y % 16 = 4 ∨ y % 16 = 5 ∨ y % 16 = 6 ∨ y % 16 = 7 ∨ y % 16 = 8 ∨ y % 16 = 9 ∨ y % 16 = 10 ∨ y % 16 = 11 ∨ y % 16 = 12 ∨ y % 16 = 13 ∨ y % 16 = 14 ∨ y % 16 = 15 := by 
      omega 
    rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.mul_mod, Nat.add_mod, Nat.pow_two]
  omega