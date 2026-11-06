import Mathlib

open Nat

theorem number_theory_52173 (p : ℕ) (hp₁ : p.Prime) (hp₂ : (p + 2).Prime)
    (hp₃ : 3 < p) (hp₄ : 3 < p + 2) : 6 ∣ (p + 1) := by
  have h1 : p % 2 = 1 := by 
    by_contra h
    push_neg at h
    have h2 : p % 2 = 0 := by omega
    have h3 : ¬ Nat.Prime (p) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : p % 3 = 0 := by omega
    have h6 : 3 ∣ p := by omega
    have h7 : ¬ p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) 
      all_goals omega
    contradiction
  cases h4 with
  | inl h7 =>
    have h8 : (p + 2) % 3 = 0 := by omega
    have h9 : 3 ∣ (p + 2) := by omega
    have h10 : ¬ (p + 2).Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by omega) 
      all_goals omega
    contradiction
    all_goals omega
  | inr h8 =>
    have h9 : (p + 1) % 3 = 0 := by omega
    have h5 : (p + 1) % 2 = 0 := by 
      omega
    have h3 : (p + 1) % 6 = 0 := by
      omega
    exact Nat.dvd_of_mod_eq_zero h3