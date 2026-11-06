import Mathlib
open Real

theorem number_theory_142888 
(p :ℕ) (h :  Nat.Prime p ∧ 10^17 + 1 ≤ p ∧ p ≤ 10^17 + 9) : p = 10^17+3 := by
  rcases h with ⟨h_prime, h1, h2⟩
  have h3 : p ≤ 10^17 + 9 := h2
  have h4 : 10^17 + 1 ≤ p := h1
  have h5 : p = 10^17 + 1 ∨ p = 10^17 + 2 ∨ p = 10^17 + 3 ∨ p = 10^17 + 4 ∨ p = 10^17 + 5 ∨ p = 10^17 + 6 ∨ p = 10^17 + 7 ∨ p = 10^17 + 8 ∨ p = 10^17 + 9 := by
    omega
  rcases h5 with (r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9)
  · -- p = 10^17 + 1
    rw [r1] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 2
    rw [r2] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 3
    exact r3
  · -- p = 10^17 + 4
    rw [r4] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 5
    rw [r5] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 6
    rw [r6] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 7
    rw [r7] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 8
    rw [r8] at h_prime
    norm_num at h_prime
  · -- p = 10^17 + 9
    rw [r9] at h_prime
    norm_num at h_prime