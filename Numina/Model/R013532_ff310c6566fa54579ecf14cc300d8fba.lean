import Mathlib

theorem number_theory_32752 (a b c : ℤ) (h₀ : 6 ∣ a^2 + b^2 + c^2) (h₁ : 3 ∣ a * b + b * c + c * a) :
    6 ∣ a^3 + b^3 + c^3 := by
  have h4 : (a ^ 2 + b ^ 2 + c ^ 2) % 2 = 0 := by
    omega
  have h5 : (a + b + c) % 2 = 0 := by
    have h6 : a ^ 2 % 2 = a % 2 := by
      have h7 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases h7 with (h7 | h7) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h7]
    have h7 : b ^ 2 % 2 = b % 2 := by
      have h8 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases h8 with (h8 | h8) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h8]
    have h8 : c ^ 2 % 2 = c % 2 := by
      have h9 : c % 2 = 0 ∨ c % 2 = 1 := by omega
      rcases h9 with (h9 | h9) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h9]
    have h9 : (a ^ 2 + b ^ 2 + c ^ 2) % 2 = (a + b + c) % 2 := by
      simp [Int.add_emod, h6, h7, h8]
    omega
  have h6 : (a ^ 3 + b ^ 3 + c ^ 3) % 2 = 0 := by
    have h7 : a ^ 3 % 2 = a % 2 := by
      have h8 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases h8 with (h8 | h8) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h8]
    have h8 : b ^ 3 % 2 = b % 2 := by
      have h9 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases h9 with (h9 | h9) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h9]
    have h9 : c ^ 3 % 2 = c % 2 := by
      have h10 : c % 2 = 0 ∨ c % 2 = 1 := by omega
      rcases h10 with (h10 | h10) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h10]
    omega
  have h7 : (a + b + c) % 3 = 0 := by
    have h8 : (a * b + b * c + c * a) % 3 = 0 := by
      omega
    have h9 : (a + b + c) ^ 2 % 3 = 0 := by
      have h10 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
        nlinarith
      have h11 : (a ^ 2 + b ^ 2 + c ^ 2) % 3 = 0 := by
        omega
      have h12 : (a * b + b * c + c * a) % 3 = 0 := h8
      simp [h10, Int.add_emod, Int.mul_emod, h11, h12]
    have h8 : (a + b + c) % 3 = 0 := by
      have h9' : (a + b + c) ^ 2 % 3 = 0 := h9
      have : (a + b + c) % 3 = 0 := by
        have h10 : (a + b + c) % 3 = 0 ∨ (a + b + c) % 3 = 1 ∨ (a + b + c) % 3 = 2 := by omega
        rcases h10 with (h10 | h10 | h10) <;> simp [h10, pow_two, Int.add_emod, Int.mul_emod] at h9' ⊢ <;> omega
      assumption
    assumption
  have h8 : (a ^ 3 + b ^ 3 + c ^ 3) % 3 = 0 := by
    have h9 : a ^ 3 % 3 = a % 3 := by
      have h10 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      rcases h10 with (h10 | h10 | h10) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h10]
    have h10 : b ^ 3 % 3 = b % 3 := by
      have h11 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases h11 with (h11 | h11 | h11) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h11]
    have h11 : c ^ 3 % 3 = c % 3 := by
      have h12 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
      rcases h12 with (h12 | h12 | h12) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h12]
    omega
  omega