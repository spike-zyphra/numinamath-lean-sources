import Mathlib

theorem number_theory_233572 (p : ℕ) (hp : Nat.Prime p) (hp1 : Nat.Prime (2 * p + 1)) (hp2 : Nat.Prime (4 * p + 1)) :
    p = 3 := by
  by_cases h : p ≤ 5
  · -- If p ≤ 5, then p can be 2, 3, or 5
    interval_cases p <;> norm_num at hp hp1 hp2 ⊢
    <;> try { tauto }
  · -- Now we need to solve the case where p > 5.
    push_neg at h
    have hp3 : Nat.Prime (3) := by norm_num
    have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1)
    · -- p % 3 = 0
      have h6 : p % 3 = 0 := h1
      have h7 : 3 ∣ p := by omega
      have h8 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
      contradiction
    · -- p % 3 = 1
      have h7 : p % 3 = 1 := h1
      have h8 : (2 * p + 1) % 3 = 0 := by
        omega
      have h9 : 3 ∣ (2 * p + 1) := by omega
      have h10 : ¬ Nat.Prime (2 * p + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * p + 1) by omega) (by omega) (by omega)
      contradiction
    · -- p % 3 = 2
      have h8 : p % 3 = 2 := h1
      have h9 : (4 * p + 1) % 3 = 0 := by
        omega
      have h10 : 3 ∣ (4 * p + 1) := by omega
      have h11 : ¬ Nat.Prime (4 * p + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (4 * p + 1) by omega) (by omega) (by omega)
      contradiction