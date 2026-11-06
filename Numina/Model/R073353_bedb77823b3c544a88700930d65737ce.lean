import Mathlib

theorem number_theory_6173 (a b c : ℕ) :
    a^2 + b^2 = 8 * c + 3 ↔ False := by
  constructor
  · -- Forward direction: Assume a^2 + b^2 = 8c + 3, prove False
    intro h
    have h1 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
      have h : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
        omega
      rcases h with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.add_mod]
      <;> norm_num
      <;> omega 
    have h2 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
      have h : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
        omega
      rcases h with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h, Nat.add_mod]
      <;> norm_num
      <;> omega 
    have h3 : (a^2 + b^2) % 8 = 3 % 8 := by 
      omega 
    omega 
  · -- Backward direction: Assume False, prove a^2 + b^2 = 8 * c + 3
    intro h
    exfalso
    exact h