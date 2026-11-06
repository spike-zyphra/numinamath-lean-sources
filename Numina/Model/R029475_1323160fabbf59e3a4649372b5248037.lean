import Mathlib

theorem number_theory_208253 (a b : ℕ) :
    ((a + b) ^ 5 - (a ^ 5 + b ^ 5)) % 10 = 0 := by
  have h1 : (a + b) ^ 5 % 10 = (a + b) % 10 := by
    have h1 : ∀ n : ℕ, n ^ 5 % 10 = n % 10 := by
      intro n
      have h2 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, h2, Nat.add_mod, Nat.mul_mod]
    specialize h1 (a + b)
    omega
  have h2 : a ^ 5 % 10 = a % 10 := by
    have h1 : ∀ n : ℕ, n ^ 5 % 10 = n % 10 := by
      intro n
      have h2 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, h2, Nat.add_mod, Nat.mul_mod]
    specialize h1 a
    omega
  have h3 : b ^ 5 % 10 = b % 10 := by
    have h1 : ∀ n : ℕ, n ^ 5 % 10 = n % 10 := by
      intro n
      have h2 : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨ n % 10 = 8 ∨ n % 10 = 9 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [Nat.pow_mod, h2, Nat.add_mod, Nat.mul_mod]
    specialize h1 b
    omega
  have h4 : (a ^ 5 + b ^ 5) % 10 = (a + b) % 10 := by
    simp [Nat.add_mod, h2, h3]
  have h5 : (a + b) ^ 5 % 10 = (a ^ 5 + b ^ 5) % 10 := by
    omega
  omega