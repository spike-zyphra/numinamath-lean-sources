import Mathlib

theorem number_theory_127015 (a d : ℕ) (ha : a > 3) (hd : d ≠ 0)
    (h : Nat.Prime a) (h' : Nat.Prime (a + d)) (h'' : Nat.Prime (a + 2 * d)) :
    6 ∣ d := by
  have h1 : a % 2 = 1 := by
    by_contra h1
    push_neg at h1
    have : a % 2 = 0 := by omega
    have h2 : ¬ Nat.Prime a := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega) (by omega) (by omega)
    tauto
  have h2 : (a + d) % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have : (a + d) % 2 = 0 := by omega
    have h3 : ¬ Nat.Prime (a + d) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (a + d) by omega) (by omega) (by omega)
    tauto
  have h3 : (a + 2 * d) % 2 = 1 := by
    by_contra h3
    push_neg at h3
    have : (a + 2 * d) % 2 = 0 := by omega
    have h4 : ¬ Nat.Prime (a + 2 * d) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (a + 2 * d) by omega) (by omega) (by omega)
    tauto
  have h4 : d % 2 = 0 := by
    omega
  have h5 : a % 3 = 1 ∨ a % 3 = 2 := by
    by_contra h6
    push_neg at h6
    have : a % 3 = 0 := by omega
    have h7 : 3 ∣ a := by omega
    have h8 : ¬ Nat.Prime a := by
      apply Nat.not_prime_of_dvd_of_lt h7 (by omega) (by omega)
    tauto
  have h6 : (a + d) % 3 = 1 ∨ (a + d) % 3 = 2 := by
    by_contra h7
    push_neg at h7
    have : (a + d) % 3 = 0 := by omega
    have h8 : 3 ∣ (a + d) := by omega
    have h9 : ¬ Nat.Prime (a + d) := by
      apply Nat.not_prime_of_dvd_of_lt h8 (by omega) (by omega)
    tauto
  have h7 : (a + 2 * d) % 3 = 1 ∨ (a + 2 * d) % 3 = 2 := by
    by_contra h8
    push_neg at h8
    have : (a + 2 * d) % 3 = 0 := by omega
    have h9 : 3 ∣ (a + 2 * d) := by omega
    have h10 : ¬ Nat.Prime (a + 2 * d) := by
      apply Nat.not_prime_of_dvd_of_lt h9 (by omega) (by omega)
    tauto
  have h8 : d % 3 = 0 := by
    omega
  omega