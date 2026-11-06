import Mathlib

theorem number_theory_191002 (p : ℕ) (hp : p.Prime) (h : p > 7) :
    240 ∣ (p ^ 4 - 1) := by
  have h1 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h3
    push_neg at h3
    have h4 : p % 3 = 0 := by omega
    have h5 : 3 ∣ p := by
      omega
    have h6 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h5
      all_goals linarith
    contradiction
  have h3 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    by_contra h4
    push_neg at h4
    have h5 : p % 5 = 0 := by omega
    have h6 : 5 ∣ p := by
      omega
    have h7 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h6
      all_goals linarith
    contradiction
  have h4 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by
    have : p % 2 = 1 := h1
    omega
  have h5 : p ^ 4 % 16 = 1 := by
    rcases h4 with (h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Nat.mul_mod]
    <;> omega
  have h6 : p ^ 4 % 3 = 1 := by
    rcases h2 with (h2 | h2)
    · simp [h2, pow_succ, Nat.mul_mod]
    · simp [h2, pow_succ, Nat.mul_mod]
  have h7 : p ^ 4 % 5 = 1 := by
    rcases h3 with (h3 | h3 | h3 | h3)
    · simp [h3, pow_succ, Nat.mul_mod]
    · simp [h3, pow_succ, Nat.mul_mod]
    · simp [h3, pow_succ, Nat.mul_mod]
    · simp [h3, pow_succ, Nat.mul_mod]
  have h8 : (p ^ 4 - 1) % 16 = 0 := by
    omega
  have h9 : (p ^ 4 - 1) % 3 = 0 := by
    omega
  have h10 : (p ^ 4 - 1) % 5 = 0 := by
    omega
  omega