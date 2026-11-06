import Mathlib

theorem number_theory_276031 (n : ℕ) :
    7 ∣ 3^(2*n + 2) - 2^(n + 1) := by

  have h1 : ∀ n : ℕ, (3 ^ (2 * n + 2) : ℕ) % 7 = (2 ^ (n + 1) : ℕ) % 7 := by
    intro n 
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      have h2 : (3 ^ (2 * (n + 1) + 2) : ℕ) % 7 = (3 ^ (2 * n + 2) * 9) % 7 := by
        ring_nf
      rw [h2]
      have h3 : (2 ^ (n + 1 + 1) : ℕ) % 7 = (2 ^ (n + 1) * 2) % 7 := by
        ring_nf
      rw [h3]
      simp [Nat.mul_mod, ih] at *
      all_goals omega
  
  have h3 : (3 ^ (2 * n + 2) : ℕ) % 7 = (2 ^ (n + 1) : ℕ) % 7 := h1 n

  have h4 : 7 ∣ (3^(2*n + 2) - 2^(n + 1) : ℕ) := by 
    omega

  exact h4