import Mathlib

theorem number_theory_259051 (p : ℕ) (hp : Nat.Prime p)
    (h : Nat.Prime (8 * p ^ 2 + 1)) :
    Nat.Prime (8 * p ^ 2 - p + 2) := by 
  by_cases h3 : p ≤ 3
  · interval_cases p <;> norm_num at hp h ⊢ <;> tauto
  · -- Assume p > 3
    have h4 : p > 3 := by
      linarith
    have h5 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h6
      push_neg at h6
      have h7 : p % 3 = 0 := by
        omega
      have h8 : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by
          omega
        ) (by nlinarith) (by nlinarith)
      contradiction
    rcases h5 with (h5 | h5)
    · -- p ≡ 1 (mod 3)
      have h6 : (8 * p ^ 2 + 1) % 3 = 0 := by
        have hp1 : p % 3 = 1 := by
          omega
        have hp2 : p ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, hp1]
        omega
      have h7 : ¬Nat.Prime (8 * p ^ 2 + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by
          omega
        ) (by nlinarith) (by nlinarith)
      contradiction
    · -- p ≡ 2 (mod 3)
      have h6 : (8 * p ^ 2 + 1) % 3 = 0 := by
        have hp2 : p % 3 = 2 := by
          omega
        have hp3 : p ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, hp2]
        omega
      have h7 : ¬Nat.Prime (8 * p ^ 2 + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p ^ 2 + 1) by
          omega
        ) (by nlinarith) (by nlinarith)
      contradiction