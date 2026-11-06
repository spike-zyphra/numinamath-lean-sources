import Mathlib

theorem number_theory_115316 (p : ℕ) (hp : Nat.Prime p) (h : 7 ≤ p) :
    240 ∣ p^4 - 1 := by 
  have h1 : p % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have : p % 2 = 0 := by omega
    have h3 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by linarith) (by linarith)
    tauto
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    have hne : p % 3 ≠ 0 := by
      by_contra h0
      have : p % 3 = 0 := by omega
      have h3 : 3 ∣ p := by omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by linarith) (by linarith)
      tauto
    omega
  have h3 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have hne : p % 5 ≠ 0 := by
      by_contra h0
      have : p % 5 = 0 := by omega
      have h3 : 5 ∣ p := by omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by linarith) (by linarith)
      tauto
    omega
  have h4 : p ^ 4 % 16 = 1 := by 
    have h51 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by 
      omega
    rcases h51 with (h51 | h51 | h51 | h51 | h51 | h51 | h51 | h51) <;> 
      simp [h51, Nat.pow_mod]
  have h5 : p ^ 4 % 3 = 1 := by 
    rcases h2 with (h2 | h2) <;> 
      simp [h2, Nat.pow_mod]
  have h6 : p ^ 4 % 5 = 1 := by
    rcases h3 with (h3 | h3 | h3 | h3) <;> 
      simp [h3, Nat.pow_mod]
  have h7 : (p ^ 4 - 1) % 16 = 0 := by
    omega
  have h8 : (p ^ 4 - 1) % 3 = 0 := by 
    omega
  have h9 : (p ^ 4 - 1) % 5 = 0 := by 
    omega
  omega