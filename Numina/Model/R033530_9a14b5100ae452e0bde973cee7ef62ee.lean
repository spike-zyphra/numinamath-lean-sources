import Mathlib

theorem number_theory_250936 (n : ℕ) (h : Odd n) : ∃ p, n^2 = 8 * p + 1 := by 
  have h2 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have h1 : n % 2 = 1 := by
      obtain ⟨k, hk⟩ := h
      omega
    omega
  have h3 : (n ^ 2) % 8 = 1 := by
    rcases h2 with (h2 | h2 | h2 | h2)
    · 
      simp [Nat.pow_mod, h2, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h2, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h2, Nat.mul_mod]
    · 
      simp [Nat.pow_mod, h2, Nat.mul_mod]
  have h4 : ∃ p, n ^ 2 = 8 * p + 1 := by
    have h5 : (n ^ 2) % 8 = 1 := h3
    have h6 : 8 ∣ (n ^ 2 - 1) := by
      omega
    rcases h6 with ⟨p, hp⟩
    use p
    omega
  exact h4