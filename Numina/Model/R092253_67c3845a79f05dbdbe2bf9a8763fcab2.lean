import Mathlib

theorem number_theory_240398 (a b : ℕ) (h₀ : a % 3 = 2) (h₁ : b % 3 = 2) : (a * b) % 3 = 1 := by 
  simp [Nat.mul_mod, h₀, h₁]