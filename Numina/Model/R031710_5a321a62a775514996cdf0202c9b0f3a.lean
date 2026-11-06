import Mathlib

theorem number_theory_268265 (n : ℕ) (h₀ : Odd n) : 96 ∣ n^4 + 2 * n^2 + 2013 := by
  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := h₀
    omega
  have h2 : (n ^ 4 + 2 * n ^ 2 + 2013) % 3 = 0 := by 
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h3 with (h3 | h3 | h3)
    · -- If n % 3 = 0
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h3]
    · -- If n % 3 = 1
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h3]
    · -- If n % 3 = 2
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h3]
  have h3 : (n ^ 4 + 2 * n ^ 2 + 2013) % 32 = 0 := by 
    have h16 : n % 2 = 1 := h1
    have h8 : n % 32 = 1 ∨ n % 32 = 3 ∨ n % 32 = 5 ∨ n % 32 = 7 ∨ n % 32 = 9 ∨ n % 32 = 11 ∨ n % 32 = 13 ∨ n % 32 = 15 ∨ n % 32 = 17 ∨ n % 32 = 19 ∨ n % 32 = 21 ∨ n % 32 = 23 ∨ n % 32 = 25 ∨ n % 32 = 27 ∨ n % 32 = 29 ∨ n % 32 = 31 := by 
      have h5 : n % 2 = 1 := h1
      omega
    rcases h8 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h]
  omega