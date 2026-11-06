import Mathlib

theorem number_theory_229538 (a b c : ℕ) :
    (a^2 + b^2 + c^2) % 8 ≠ 7 := by
  have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
    omega
  have h2 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
    omega
  have h3 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
    omega
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 <;> simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h1, h2, h3]