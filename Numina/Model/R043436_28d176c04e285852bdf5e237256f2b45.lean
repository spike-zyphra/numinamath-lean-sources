import Mathlib

theorem number_theory_14979 (p : ℕ) (hp : p.Prime)
    (h : ∃ d, d = 6 ∧ (p + d).Prime ∧ (p + 2 * d).Prime ∧ (p + 3 * d).Prime ∧ (p + 4 * d).Prime) :
    p + (p + 6) + (p + 12) + (p + 18) + (p + 24) = 85 := by

  rcases h with ⟨d, h1, hp1, hp2, hp3, hp4⟩
  subst h1

  by_cases h2 : p ≤ 29
  · interval_cases p <;> norm_num at hp hp1 hp2 hp3 hp4 ⊢ <;> try { tauto }

  · push_neg at h2

    have h31 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      omega

    rcases h31 with (h5 | h5 | h5 | h5 | h5)

    · -- Assume p ≡ 0 (mod 5)
      have h6 : p % 5 = 0 := h5
      have h4 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show (5 : ℕ) ∣ p by omega)
        all_goals omega
      contradiction

    · -- Assume p ≡ 1 (mod 5)
      have h7 : (p + 24) % 5 = 0 := by
        omega
      have h4 : ¬(p + 24).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show (5 : ℕ) ∣ (p + 24) by omega)
        all_goals omega
      contradiction

    · -- Assume p ≡ 2 (mod 5)
      have h7 : (p + 18) % 5 = 0 := by
        omega
      have h4 : ¬(p + 18).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show (5 : ℕ) ∣ (p + 18) by omega)
        all_goals omega
      contradiction

    · -- Assume p ≡ 3 (mod 5)
      have h7 : (p + 12) % 5 = 0 := by
        omega
      have h4 : ¬(p + 12).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show (5 : ℕ) ∣ (p + 12) by omega)
        all_goals omega
      contradiction

    · -- Assume p ≡ 4 (mod 5)
      have h7 : (p + 6) % 5 = 0 := by
        omega
      have h4 : ¬(p + 6).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show (5 : ℕ) ∣ (p + 6) by omega)
        all_goals omega
      contradiction