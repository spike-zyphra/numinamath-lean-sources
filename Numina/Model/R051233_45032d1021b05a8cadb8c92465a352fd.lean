import Mathlib

theorem number_theory_254616 (p : ℕ) (hp : p.Prime) :
    (p^2 - 1) % 12 = 3 ∨ (p^2 - 1) % 12 = 8 ∨ (p^2 - 1) % 12 = 0 := by
  have h1 : p ≥ 2 := Nat.Prime.two_le hp
  by_cases h2 : p ≤ 3
  · -- When p ≤ 3, then p can be 2 or 3.
    interval_cases p <;> norm_num at *
    <;> omega
  · -- Case where p > 3
    have h3 : p > 3 := by omega
    have h4 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
      by_contra h
      push_neg at h
      have h5 : p % 2 = 0 ∨ p % 3 = 0 := by
        omega
      rcases h5 with (h5 | h5)
      · -- p is even and greater than 2, so not prime
        have h6 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p divisible by 3 and greater than 3, so not prime
        have h6 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
    rcases h4 with (h | h | h | h)
    · -- p ≡ 1 [MOD 12]
      have : (p ^ 2) % 12 = 1 := by
        norm_num [Nat.pow_mod, h]
      have h0 : (p^2 - 1) % 12 = 0 := by
        omega
      simp [h0]
    · -- p ≡ 5 [MOD 12]
      have : (p ^ 2) % 12 = 1 := by
        norm_num [Nat.pow_mod, h]
      have h0 : (p^2 - 1) % 12 = 0 := by
        omega
      simp [h0]
    · -- p ≡ 7 [MOD 12]
      have : (p ^ 2) % 12 = 1 := by
        norm_num [Nat.pow_mod, h]
      have h0 : (p^2 - 1) % 12 = 0 := by
        omega
      simp [h0]
    · -- p ≡ 11 [MOD 12]
      have : (p ^ 2) % 12 = 1 := by
        norm_num [Nat.pow_mod, h]
      have h0 : (p^2 - 1) % 12 = 0 := by
        omega
      simp [h0]