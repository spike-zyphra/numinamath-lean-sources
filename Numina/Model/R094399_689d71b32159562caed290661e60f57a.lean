import Mathlib

theorem number_theory_275848 (n : ℕ) (h₀ : Odd n) (h₁ : Odd (n + 2)) :
    8 ∣ (n + 2)^2 - n^2 := by
  have h2 : n % 2 = 1 := by 
    rcases h₀ with ⟨k, hk⟩ 
    omega
  have h3 : (n % 8 = 1) ∨ (n % 8 = 3) ∨ (n % 8 = 5) ∨ (n % 8 = 7) := by
    have h4 : n % 2 = 1 := h2
    omega
  rcases h3 with (h | h | h | h)
  · -- Case n % 8 = 1
    have h4 : (n + 2) % 8 = 3 := by omega
    have h5 : (n + 2)^2 % 8 = 1 := by
      simp [Nat.pow_mod, h4]
    have h6 : n^2 % 8 = 1 := by
      simp [Nat.pow_mod, h]
    omega
  · -- Case n % 8 = 3
    have h4 : (n + 2) % 8 = 5 := by omega
    have h5 : (n + 2)^2 % 8 = 1 := by
      simp [Nat.pow_mod, h4]
    have h6 : n^2 % 8 = 1 := by
      simp [Nat.pow_mod, h]
    omega
  · -- Case n % 8 = 5
    have h4 : (n + 2) % 8 = 7 := by omega
    have h5 : (n + 2)^2 % 8 = 1 := by
      simp [Nat.pow_mod, h4]
    have h6 : n^2 % 8 = 1 := by
      simp [Nat.pow_mod, h]
    omega
  · -- Case n % 8 = 7
    have h4 : (n + 2) % 8 = 1 := by omega
    have h5 : (n + 2)^2 % 8 = 1 := by
      simp [Nat.pow_mod, h4]
    have h6 : n^2 % 8 = 1 := by
      simp [Nat.pow_mod, h]
    omega