import Mathlib

theorem number_theory_131150 (a b : ℕ) (h₀ : a^2 + b^2 ≡ 0 [MOD 7]) :
    49 ∣ a * b := by
  have h1 : a ^ 2 % 7 = 0 ∨ a ^ 2 % 7 = 1 ∨ a ^ 2 % 7 = 2 ∨ a ^ 2 % 7 = 4 := by
    have h : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h with (h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h]
  have h2 : b ^ 2 % 7 = 0 ∨ b ^ 2 % 7 = 1 ∨ b ^ 2 % 7 = 2 ∨ b ^ 2 % 7 = 4 := by
    have h : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
      omega
    rcases h with (h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h]
  have h3 : (a ^ 2 + b ^ 2) % 7 = 0 := by
    norm_num [Nat.ModEq] at h₀ ⊢
    omega
  have h4 : a ^ 2 % 7 = 0 := by 
    omega
  have h5 : b ^ 2 % 7 = 0 := by 
    omega
  have h6 : a % 7 = 0 := by
    have h7 : a ^ 2 % 7 = 0 := h4
    have h8 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
      omega
    rcases h8 with (h | h | h | h | h | h | h) <;> norm_num [pow_two, Nat.mul_mod, h] at h7 <;> omega
  have h7 : b % 7 = 0 := by 
    have h8 : b ^ 2 % 7 = 0 := h5
    have h9 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
      omega
    rcases h9 with (h | h | h | h | h | h | h) <;> norm_num [pow_two, Nat.mul_mod, h] at h8 <;> omega
  have h10 : 7 ∣ a := by 
    omega
  have h11 : 7 ∣ b := by 
    omega
  obtain ⟨k, hk⟩ := h10
  obtain ⟨m, hm⟩ := h11
  rw [show a = 7 * k by omega, show b = 7 * m by omega]
  use (k * m)
  all_goals ring