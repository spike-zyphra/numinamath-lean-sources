import Mathlib

theorem number_theory_8398
    (a b c : ℤ) :
    a ^ 2 + b ^ 2 - 8 * c ≠ 6 := by
-- Assume equality and derive a contradiction
  by_contra h
  have h₁ : a ^ 2 + b ^ 2 - 8 * c = 6 := h
-- Simplify modular expressions
  have h2 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
    have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
  have h3 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
    have h1 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by 
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
  omega