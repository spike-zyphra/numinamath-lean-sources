import Mathlib

theorem number_theory_188855 (p : ℕ) (hp : p.Prime) (h : 5 ≤ p) :
    24 ∣ (p^2 - 1) := by
  have h1 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
    have h2 : p % 2 ≠ 0 := by
      by_contra h'
      have : ¬ p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
      contradiction
    have h3 : p % 3 ≠ 0 := by
      by_contra h'
      have : 3 ∣ p := by
        omega
      have : ¬ p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
      contradiction
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
  · -- case p % 24 = 1
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 5
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 7
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 11
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 13
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 17
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 19
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3
  · -- case p % 24 = 23
    have h2 : p^2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h1]
    have h3 : 24 ∣ (p^2 - 1) := by
      omega
    exact h3