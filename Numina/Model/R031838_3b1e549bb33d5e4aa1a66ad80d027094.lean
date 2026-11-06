import Mathlib

theorem number_theory_234617 (n : ℕ) (h₀ : n > 0) (h₁ : Nat.Prime n) (h₂ : Nat.Prime (n + 7)) (h₃ : Nat.Prime (n + 14)) :
    (n + 6) % 7 = 4 := by 
  have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h4 with (h4 | h4 | h4)
  · -- Assume n ≡ 0 (mod 3)
    have h5 : n % 3 = 0 := h4
    by_cases h6 : n > 3
    · -- Assume n > 3
      have h7 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega)
        all_goals omega
      contradiction
    · -- Assume n ≤ 3
      have h6 : n ≤ 3 := by linarith
      interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢
  · -- Assume n ≡1 (mod3)
    have h5 : n % 3 = 1 := h4
    have h8 : (n + 14) % 3 = 0 := by 
      omega
    have h9 : ¬ Nat.Prime (n + 14) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n + 14) by omega)
      all_goals omega
    contradiction
  · -- Assume n ≡2 (mod3)
    have h5 : n % 3 = 2 := h4
    by_cases h6 : n ≤ 23
    · -- Assume n ≤ 23
      interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢
    · -- Assume n > 23
      push_neg at h6
      have h14 : (n + 7) % 3 = 0 := by
        omega
      have h15 : ¬ Nat.Prime (n + 7) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n + 7) by omega)
        all_goals omega
      contradiction