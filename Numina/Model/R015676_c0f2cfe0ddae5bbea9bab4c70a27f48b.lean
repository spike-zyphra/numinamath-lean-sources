import Mathlib

theorem number_theory_215669 : IsGreatest {n | ∃ a, ∀ i ∈ Finset.range n, Nat.Prime (a + 6 * i)} 5 := by
  constructor
  · -- Show 5 is achievable
    use 5
    intro i hi
    rw [Finset.mem_range] at hi
    interval_cases i <;> norm_num
  · -- Show it's maximum
    intro n hn
    rcases hn with ⟨a, ha⟩
    by_contra h
    push_neg at h
    have h1 : Nat.Prime (a + 6 * 0) := by
      apply ha 0 (by
        simp at h ⊢
        all_goals omega
      )
    have h2 : Nat.Prime (a + 6 * 1) := by
      apply ha 1 (by
        simp at h ⊢
        all_goals omega
      )
    have h3 : Nat.Prime (a + 6 * 2) := by
      apply ha 2 (by
        simp at h ⊢
        all_goals omega
      )
    have h4 : Nat.Prime (a + 6 * 3) := by
      apply ha 3 (by
        simp at h ⊢
        all_goals omega
      )
    have h5 : Nat.Prime (a + 6 * 4) := by
      apply ha 4 (by
        simp at h ⊢
        all_goals omega
      )
    have h6 : Nat.Prime (a + 6 * 5) := by
      apply ha 5 (by
        simp at h ⊢
        all_goals omega
      )
    by_cases h7 : a % 5 = 0
    · -- If a ≡ 0 [mod 5], then a is divisible by 5. Since it's prime, it's 5.
      by_cases ha5 : a > 5
      · -- If a > 5, then a cannot be prime
        have h9 : ¬ Nat.Prime a := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ a by omega)
          all_goals omega
        contradiction
      · -- So a ≤ 5
        interval_cases a <;> norm_num at h1 h2 h3 h4 h5 h6
    · -- a % 5 = 1, 2, 3, or 4
      by_cases h8 : a % 5 = 1
      · -- If a ≡ 1 [mod 5], then a + 24 ≡ 0 [mod 5]
        have h9 : (a + 6 * 4) % 5 = 0 := by
          omega
        have h10 : ¬ Nat.Prime (a + 6 * 4) := by
          apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (a + 6 * 4) by omega)
          all_goals omega
        contradiction
      · -- If a % 5 = 2, 3, or 4
        by_cases h9 : a % 5 = 2
        · -- If a ≡ 2 [mod 5], then a + 18 ≡ 0 [mod 5]
          have h10 : (a + 6 * 3) % 5 = 0 := by
            omega
          have h11 : ¬ Nat.Prime (a + 6 * 3) := by
            apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (a + 6 * 3) by omega)
            all_goals omega
          contradiction
        · -- If a % 5 = 3 or 4
          by_cases h10 : a % 5 = 3
          · -- If a ≡ 3 [mod 5], then a + 12 ≡ 0 [mod 5]
            have h11 : (a + 6 * 2) % 5 = 0 := by
              omega
            have h12 : ¬ Nat.Prime (a + 6 * 2) := by
              apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (a + 6 * 2) by omega)
              all_goals omega
            contradiction
          · -- If a ≡ 4 [mod 5]
            have h11 : a % 5 = 4 := by
              omega
            have h12 : (a + 6 * 1) % 5 = 0 := by
              omega
            have h13 : ¬ Nat.Prime (a + 6 * 1) := by
              apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (a + 6 * 1) by omega)
              all_goals omega
            contradiction