import Mathlib

theorem number_theory_283462 (p : ℕ) (hp : p.Prime) (h : p > 3) :
    p^2 ≡ 1 [MOD 12] := by

  have h1 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have h2' : p % 2 = 0 := by omega
    have h2 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    tauto

  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h2 : p % 3 ≠ 0 := by
      by_contra h2
      have h2' : p % 3 = 0 := by omega
      have h3 : 3 ∣ p := by omega
      have h4 : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith
      tauto
    omega

  have h3 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
    have h4 : p % 2 = 1 := h1
    have h5 : p % 3 = 1 ∨ p % 3 = 2 := h2
    omega

  rcases h3 with (h3 | h3 | h3 | h3)

  · -- p % 12 = 1
    simp [Nat.ModEq, Nat.pow_mod, h3]

  · -- p % 12 = 5
    simp [Nat.ModEq, Nat.pow_mod, h3]

  · -- p % 12 = 7
    simp [Nat.ModEq, Nat.pow_mod, h3]

  · -- p % 12 = 11
    simp [Nat.ModEq, Nat.pow_mod, h3]