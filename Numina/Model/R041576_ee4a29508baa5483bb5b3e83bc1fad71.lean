import Mathlib

theorem number_theory_210000 (a b c d N : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : d > 0) (h₄ : N > 5) (h₅ : Nat.gcd a b = 1) (h₆ : Nat.gcd a c = 2)
    (h₇ : Nat.gcd a d = 3) (h₈ : Nat.gcd b c = 4) (h₉ : Nat.gcd b d = 5)
    (h₁₀ : Nat.gcd c d = N) :
    N = 14 := by
  have h1 : a % 2 = 0 := by 
    have h2 : 2 ∣ a := by
      have h_gcd : Nat.gcd a c = 2 := h₆
      have h21 : Nat.gcd a c ∣ a := by apply Nat.gcd_dvd_left
      have h22 : Nat.gcd a c = 2 := h_gcd
      rw [h22] at h21
      exact h21
    omega
  have h2 : b % 2 = 0 := by 
    have h4 : 4 ∣ b := by
      have h_gcd : Nat.gcd b c = 4 := h₈
      have h21 : Nat.gcd b c ∣ b := by apply Nat.gcd_dvd_left
      have h22 : Nat.gcd b c = 4 := h_gcd
      rw [h22] at h21
      exact h21
    omega
  have h3 : Nat.gcd a b > 1 := by
    have h4 : a % 2 = 0 := h1
    have h5 : b % 2 = 0 := h2
    have h6 : 2 ∣ a := by 
      omega
    have h7 : 2 ∣ b := by 
      omega
    have h8 : 2 ∣ Nat.gcd a b := by 
      exact Nat.dvd_gcd h6 h7
    have h9 : Nat.gcd a b ≥ 2 := by 
      omega
    linarith
  have h4 : Nat.gcd a b = 1 := h₅
  linarith