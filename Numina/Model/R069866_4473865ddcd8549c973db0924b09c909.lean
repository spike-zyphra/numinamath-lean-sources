import Mathlib

theorem number_theory_113082 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (p + 15)) :
    p = 2 := by
  by_cases h1 : p ≤ 2
  · interval_cases p <;> norm_num at hp h <;> omega

  · -- Case where p > 2

    -- First, we derive p ≡ 1 mod 2 (p is odd)
    have h2 : p % 2 = 1 := by
      by_contra h'
      push_neg at h'
      have h1 : p % 2 = 0 := by
        omega
      have h2 : p > 2 := by
        linarith
      have : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction

    -- Now, because p ≡ 1 mod 2 (p is odd)
    -- We derive p + 15 ≡ 1 + 1 ≡ 0 mod 2 (which is even)
    have h4 : (p + 15) % 2 = 0 := by
      omega

    -- Since p + 15 ≡ 0 mod 2, it's even
    -- But p > 2, so p >= 3, hence p + 15 >= 3 + 15 = 18 (which is composite)
    have h5 : ¬ Nat.Prime (p + 15) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (p + 15) by omega)
      all_goals omega
      all_goals nlinarith

    contradiction