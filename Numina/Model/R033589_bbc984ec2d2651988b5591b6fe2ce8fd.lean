import Mathlib

theorem number_theory_178766 (a b : ℤ) :
    11 ∣ a^2 + b^2 ↔ 11 ∣ a^2 ∧ 11 ∣ b^2 := by 
  constructor 
  · -- Forward direction: if 11 divides a^2 + b^2, then 11 divides a^2 and b^2 
    intro h 
    have h1 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by 
      omega 
    have h2 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by 
      omega 
    have h3 : (a ^ 2 + b ^ 2) % 11 = 0 := by 
      omega 
    have h4 : a ^ 2 % 11 = 0 := by 
      have h8 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := h1 
      have h9 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := h2 
      have h10 : (a ^ 2 + b ^ 2) % 11 = 0 := h3 
      have : a ^ 2 % 11 = 0 := by 
        rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8) <;> rcases h9 with (h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9) <;> 
          simp [Int.add_emod, pow_two, Int.mul_emod, h8, h9] at h10 ⊢ 
          <;> omega 
      assumption 
    have h5 : b ^ 2 % 11 = 0 := by 
      have h8 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := h1 
      have h9 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := h2 
      have h10 : (a ^ 2 + b ^ 2) % 11 = 0 := h3 
      have : b ^ 2 % 11 = 0 := by 
        rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8) <;> rcases h9 with (h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9) <;> 
          simp [Int.add_emod, pow_two, Int.mul_emod, h8, h9] at h10 ⊢ 
          <;> omega 
      assumption 
    constructor 
    · -- Show that 11 divides a^2 
      exact Int.dvd_of_emod_eq_zero h4 
    · -- Show that 11 divides b^2 
      exact Int.dvd_of_emod_eq_zero h5 
  · -- Backward direction: if 11 divides a^2 and b^2, then 11 divides a^2 + b^2 
    rintro ⟨h1, h2⟩ 
    have h3 : 11 ∣ a^2 := h1 
    have h4 : 11 ∣ b^2 := h2 
    omega