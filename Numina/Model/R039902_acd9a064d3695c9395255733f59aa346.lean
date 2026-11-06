import Mathlib

theorem number_theory_120722 (p : ℕ) (hp : Nat.Prime p)
    (h1 : Nat.Prime (4 * p ^ 2 + 1)) (h2 : Nat.Prime (6 * p ^ 2 + 1)) :
    p = 5 := by
  by_cases h : p ≤ 5
  · interval_cases p <;> norm_num at hp h1 h2 ⊢
    <;> try { tauto }
  · -- p > 5
    have h3 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        by_contra h'
        push_neg at h'
        have : p % 5 = 0 := by omega
        have h4 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
          all_goals
          omega
        contradiction
      assumption
    rcases h3 with (h3 | h3 | h3 | h3)
    · -- p % 5 = 1
      have h4 : (4 * p ^ 2 + 1) % 5 = 0 := by
        have h5 : p % 5 = 1 := h3
        have h6 : p ^ 2 % 5 = 1 := by
          simp [Nat.pow_mod, h5]
        omega
      have h41 : ¬ Nat.Prime (4 * p ^ 2 + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
        all_goals
        nlinarith
        all_goals nlinarith
      contradiction
    · -- p % 5 = 2
      have h7 : (6 * p ^ 2 + 1) % 5 = 0 := by
        have h8 : p % 5 = 2 := h3
        have h9 : p ^ 2 % 5 = 4 := by
          simp [Nat.pow_mod, h8]
        omega
      have h71 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
        all_goals
        nlinarith
      contradiction
    · -- p % 5 = 3
      have h7 : (6 * p ^ 2 + 1) % 5 = 0 := by
        have h8 : p % 5 = 3 := h3
        have h9 : p ^ 2 % 5 = 4 := by
          simp [Nat.pow_mod, h8]
        omega
      have h71 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (6 * p ^ 2 + 1) by omega)
        all_goals
        nlinarith
      contradiction
    · -- p % 5 = 4
      have h4 : (4 * p ^ 2 + 1) % 5 = 0 := by
        have h5 : p % 5 = 4 := h3
        have h6 : p ^ 2 % 5 = 1 := by
          simp [Nat.pow_mod, h5]
        omega
      have h41 : ¬ Nat.Prime (4 * p ^ 2 + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (4 * p ^ 2 + 1) by omega)
        all_goals
        nlinarith
      contradiction