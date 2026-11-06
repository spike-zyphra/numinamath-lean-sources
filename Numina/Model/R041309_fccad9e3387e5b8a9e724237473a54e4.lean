import Mathlib
theorem number_theory_284885 (p : ℕ) (hp : p.Prime) (h : p > 3) : (p ^ 2) % 12 = 1:= by
  have h1 : p % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h3
    push_neg at h3
    have h3' : p % 3 = 0 := by omega
    have : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals linarith
    contradiction
  have h3 : p % 2 = 1 := h1
  have h4 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
    omega
  rcases h4 with (h | h | h | h)
  · -- p ≡ 1 [MOD 12]
    simp [Nat.pow_mod, h, Nat.mul_mod]
  · -- p ≡ 5 [MOD 12]
    simp [Nat.pow_mod, h, Nat.mul_mod]
  · -- p ≡ 7 [MOD 12]
    simp [Nat.pow_mod, h, Nat.mul_mod]
  · -- p ≡ 11 [MOD 12]
    simp [Nat.pow_mod, h, Nat.mul_mod]