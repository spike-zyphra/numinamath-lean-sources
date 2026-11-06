import Mathlib

theorem number_theory_282057 (p : ℕ) (hp : Nat.Prime p) (h8p1 : Nat.Prime (8 * p - 1)) :
    ¬Nat.Prime (8 * p + 1) := by
  by_contra h
  have h1 : p ≥ 2 := Nat.Prime.two_le hp
  have h2 : 8 * p - 1 ≥ 2 := by
    have h8p1' : Nat.Prime (8 * p - 1) := h8p1
    have := Nat.Prime.two_le h8p1'
    omega
  have h3 : 8 * p + 1 ≥ 2 := by
    omega
  by_cases h4 : p ≤ 3
  · -- p is 2 or 3
    interval_cases p <;> norm_num at hp h8p1 h <;> tauto
  · -- p > 3
    push_neg at h4
    have h5 : p % 3 = 1 ∨ p % 3 = 2 := by
      have h5 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h6 : p % 3 = 0 := by
          omega
        have h7 : p > 3 := by linarith
        have h8 : p % 3 = 0 := h6
        have h9 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      tauto
    rcases h5 with (h5 | h5)
    · -- p ≡ 1 (mod 3)
      have h8 : (8 * p + 1) % 3 = 0 := by
        omega
      have h9 : ¬Nat.Prime (8 * p + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p + 1) by omega)
        all_goals
        have hp1 : p ≥ 4 := by linarith
        omega
      contradiction
    · -- p ≡ 2 (mod 3)
      have h8 : (8 * p - 1) % 3 = 0 := by
        omega
      have h9 : ¬Nat.Prime (8 * p - 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (8 * p - 1) by omega)
        all_goals
        have hp1 : p ≥ 4 := by linarith
        omega
      contradiction