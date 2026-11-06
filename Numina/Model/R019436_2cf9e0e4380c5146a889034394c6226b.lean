import Mathlib

theorem number_theory_327837 (a b c : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) :
    3 ∣ a ∨ 3 ∣ b := by
  by_contra h
  push_neg at h
  have h4 : a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have h5 : b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  have h6 : a ^ 2 % 3 = 1 := by
    rcases h4 with (h | h)
    · -- a % 3 = 1
      simp [Nat.pow_mod, h, Nat.mul_mod]
    · -- a % 3 = 2
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h7 : b ^ 2 % 3 = 1 := by
    rcases h5 with (h | h)
    · -- b % 3 = 1
      simp [Nat.pow_mod, h, Nat.mul_mod]
    · -- b % 3 = 2
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h8 : (a ^ 2 + b ^ 2) % 3 = 2 := by
    omega
  have h9 : c ^ 2 % 3 = 0 ∨ c ^ 2 % 3 = 1 := by 
    have h10 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by 
      omega
    rcases h10 with (h | h | h)
    · -- c % 3 = 0
      simp [Nat.pow_mod, h, Nat.mul_mod]
    · -- c % 3 = 1
      simp [Nat.pow_mod, h, Nat.mul_mod]
    · -- c % 3 = 2
      simp [Nat.pow_mod, h, Nat.mul_mod]
  have h10 : (a ^ 2 + b ^ 2) % 3 = c ^ 2 % 3 := by
    omega
  omega