import Mathlib

theorem number_theory_232979 (m s : ℕ) (h₀ : ∃ a, m = a^2) (h₁ : ∃ b, s = b^2)
    (h₂ : (m - s) % 10 = 2) (h₃ : m % 10 > s % 10) :
    m % 10 = 6 ∧ s % 10 = 4 := by
  rcases h₀ with ⟨a, rfl⟩
  rcases h₁ with ⟨b, rfl⟩

  have h1 : a^2 % 10 = 0 ∨ a^2 % 10 = 1 ∨ a^2 % 10 = 4 ∨ a^2 % 10 = 5 ∨ a^2 % 10 = 6 ∨ a^2 % 10 = 9 := by
    have h1 : a % 10 = 0 ∨ a % 10 = 1 ∨ a % 10 = 2 ∨ a % 10 = 3 ∨ a % 10 = 4 ∨ a % 10 = 5 ∨ a % 10 = 6 ∨ a % 10 = 7 ∨ a % 10 = 8 ∨ a % 10 = 9 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, h] at *
  
  have h2 : b^2 % 10 = 0 ∨ b^2 % 10 = 1 ∨ b^2 % 10 = 4 ∨ b^2 % 10 = 5 ∨ b^2 % 10 = 6 ∨ b^2 % 10 = 9 := by
    have h2 : b % 10 = 0 ∨ b % 10 = 1 ∨ b % 10 = 2 ∨ b % 10 = 3 ∨ b % 10 = 4 ∨ b % 10 = 5 ∨ b % 10 = 6 ∨ b % 10 = 7 ∨ b % 10 = 8 ∨ b % 10 = 9 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h | h) <;> norm_num [Nat.pow_mod, h] at *

  omega