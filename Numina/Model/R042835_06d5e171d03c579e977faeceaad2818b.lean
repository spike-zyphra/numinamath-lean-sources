import Mathlib

theorem number_theory_245231 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    96 ∣ 4 * (p ^ 2) - 100 := by
  have h1 : p % 2 = 1 := by
    by_contra h1
    push_neg at h1
    have : p % 2 = 0 := by omega
    have : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h3
      push_neg at h3
      have h4 : p % 3 = 0 := by omega
      have h5 : 3 ∣ p := by omega
      have h6 : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt h5 (by omega) (by omega)
      contradiction
    assumption
  have h5 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  have h6 : p ^ 2 % 8 = 1 := by
    rcases h5 with (h | h | h | h) <;> 
      simp [Nat.pow_mod, h]
  have h7 : p ^ 2 % 3 = 1 := by 
    rcases h2 with (h | h)
    · simp [Nat.pow_mod, h]
    · simp [Nat.pow_mod, h]
  have h8 : p ^ 2 % 24 = 1 := by
    omega
  have h9 : (4 * (p ^ 2)) % 96 = 4 := by 
    have h10 : p ^ 2 % 24 = 1 := h8
    omega
  have h100 : (4 * (p ^ 2) - 100) % 96 = 0 := by 
    omega
  omega